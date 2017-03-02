--[[
Copyright © 2015 Dynatrace LLC. 
All rights reserved. 
Unpublished rights reserved under the Copyright Laws of the United States.

U.S. GOVERNMENT RIGHTS-Use, duplication, or disclosure by the U.S. Government is
subject to restrictions as set forth in Dynatrace LLC license agreement and as
provided in DFARS 227.7202-1(a) and 227.7202-3(a) (1995), DFARS
252.227-7013(c)(1)(ii) (OCT 1988), FAR 12.212 (a) (1995), FAR 52.227-19, 
or FAR 52.227-14 (ALT III), as applicable.

This product contains confidential information and trade secrets of Dynatrace LLC. 
Disclosure is prohibited without the prior express written permission of Dynatrace LLC. 
Use of this product is subject to the terms and conditions of the user's License Agreement with Dynatrace LLC.
See the license agreement text online at https://community.dynatrace.com/community/download/attachments/5144912/dynaTraceBSD.txt?version=3&modificationDate=1441261477160&api=v2
--]]

--[[
This is Corba GIOP protocol parser.
Supported GIOP versions: 1.1, 1.2
--]]

require 'amd'


local little_endian_factors = {1, 256, 65536, 16777216}
local big_endian_factors = {16777216, 65536, 256, 1}
local GIOP = 'GIOP'

local REQUEST_MESSAGE_TYPE = 0x0
local REPLY_MESSAGE_TYPE = 0x1
local CANCEL_REQUEST_MESSAGE_TYPE = 0x2
local LOCATE_REQUEST_MESSAGE_TYPE = 0x3
local LOCATE_REPLY_MESSAGE_TYPE = 0x4
local CLOSECONNECTION_MESSAGE_TYPE = 0x5
local ERROR_MESSAGE_TYPE = 0x6
local FRAGMENT_MESSAGE_TYPE = 0x7

local NO_EXCEPTION = 0x0
local USER_EXCEPTION = 0x1
local SYSTEM_EXCEPTION = 0x2

local MAGIC_NUMBER_LEN = 4
local VERSION_LEN = 2
local MESSAGE_FLAGS_LEN = 1
local MESSAGE_TYPE_LEN = 1
local MESSAGE_SIZE_LEN = 4
local REQUEST_ID_LEN = 4
local RESPONSE_FLAGS_LEN = 1
local RESERVED_LEN = 3
local TARGET_ADDRESS_LEN = 2
local RESPONSE_EXPECTED_LEN = 1
local SEQUENCE_LENGTH_LEN = 4
local SERVICE_CONTEXT_ID_LEN = 4
local CODESETS_SERVICE_LEN = 16
local REPLY_STATUS_LEN = 4
local EXCEPTION_LENGTH_LEN = 4
local KEYADDR_LENGTH_LEN = 4
local OPERATION_LENGTH_LEN = 4

local MAGIC_NUMBER_OFFSET = 1
local VERSION_OFFSET = 5
local MESSAGE_FLAGS_OFFSET = 7
local MESSAGE_TYPE_OFFSET = 8
local MESSAGE_SIZE_OFFSET = 9
local REQUEST_ID_OFFSET = 13

local GIOP_VERSION_1_1 = 0x0101
local GIOP_VERSION_1_2 = 0x0102
local GIOP_HEADER_SIZE = 12

-- see IPayloadParser::ParserErrorCode structure on C++ side
local PARSER_ERROR_CODE = {OK=0, NEED_MORE_DATA=1, RUN_ERROR=2, OPERATION_NOT_SUPPORTED=3}

local REPLY_STATUS_TYPE = {[0]='NO_EXCEPTION', 'USER_EXCEPTION', 'SYSTEM_EXCEPTION', 'LOCATION_FORWARD',
    'LOCATION_FORWARD_PERM', 'NEEDS_ADDRESSING_MODE'}

-- see yaha::Direction enumeration on C++ side
local DIRECTION = {C2S=0, S2C=1}

local function unpack_integer4(pstr, offset, is_little_endian)
    --	struct.unpack("I4", pstr:sub(offset, offset + 4))
    local factors = (is_little_endian and little_endian_factors) or big_endian_factors
    return (pstr:byte(offset) * factors[1]) +
        (pstr:byte(offset + 1) * factors[2]) +
        (pstr:byte(offset + 2) * factors[3]) +
        (pstr:byte(offset + 3) * factors[4])
end

local function unpack_short(pstr, offset)
    --  struct.unpack(">I2", pstr:sub(offset, offset + 2))
    return (pstr:byte(offset) * 256) + (pstr:byte(offset + 1))
end

local function bit(p)
    return 2 ^ (p - 1)  -- 1-based indexing
end

-- Typical call:  if hasbit(x, bit(3)) then ...
local function hasbit(x, p)
    return x % (p + p) >= p
end

local function print_hex(pstr, offset, len)
    for idx, el in ipairs({pstr:byte(offset, offset + len)}) do
        amd.print(idx + " " + string.format('0x%0x', el))
    end
end

-- calculate effective offset of a field in GIOP message
-- according to Corba specification some fields are aligned to 2, 4 or 8 byte boundary
local function calculate_effective_field_offset(context, declared_field_length, boundary)
    local current_offset = context.offset
    while (context.offset + boundary - 1) % declared_field_length ~= 0 do
        context.offset = context.offset + 1
    end
    return context.offset
end


local function consume_servicecontext_list(pstr, context, is_little_endian)
    calculate_effective_field_offset(context, SEQUENCE_LENGTH_LEN, GIOP_HEADER_SIZE)
    local sequence_length = unpack_integer4(pstr, context.offset, is_little_endian)
    --	amd.print('sequence_length', sequence_length)
    context.offset = context.offset + SEQUENCE_LENGTH_LEN
    for seq_no=1, sequence_length do
        calculate_effective_field_offset(context, SERVICE_CONTEXT_ID_LEN, GIOP_HEADER_SIZE)
        local service_context_id = unpack_integer4(pstr, context.offset, is_little_endian)
        --		amd.print(string.format('service_context_id: 0x%04x', service_context_id))
        local consumed_bytes = SERVICE_CONTEXT_ID_LEN
        local sequence_length = unpack_integer4(pstr, context.offset + SERVICE_CONTEXT_ID_LEN, is_little_endian)
        --		amd.print('sequence_length=', sequence_length)
        -- 4-byte sequence length field:
        consumed_bytes = consumed_bytes + 4
        consumed_bytes = consumed_bytes + sequence_length
        context.offset = context.offset + consumed_bytes
    end
    return context.offset
end


--
-- public functions:
--

-- script name --
function script_name()
    return "CorbaParser"
end

-- define tables for message handlers
CorbaMessagePartHandler = {}
CorbaCompleteMessageHandler = {}


function messageHandlers()
    return {"CorbaMessagePartHandler", "CorbaCompleteMessageHandler"}
end


-- Parses Corba message and sets its size and session id.
function CorbaMessagePartHandler.parseMessage(messageHandler)
    local block = messageHandler:currentBlock()
    --    print("CorbaMessagePartHandler.parseMessage: payload_len=", block:length())

    if block:length() < GIOP_HEADER_SIZE + REQUEST_ID_LEN then
        -- message too short
        messageHandler:needMore(GIOP_HEADER_SIZE + REQUEST_ID_LEN)
        return
    end

    local payload = block:c_str()
    if payload:sub(MAGIC_NUMBER_OFFSET, MAGIC_NUMBER_LEN) ~= GIOP then
        -- not a GIOP message
        messageHandler:setBroken()
        return
    end

    local isLittleEndian = hasbit(payload:byte(MESSAGE_FLAGS_OFFSET), bit(1))
    local messageSize = unpack_integer4(payload, MESSAGE_SIZE_OFFSET, isLittleEndian)
    if payload:len() < messageSize + GIOP_HEADER_SIZE then
        -- message too short
        messageHandler:needMore(messageSize + GIOP_HEADER_SIZE)
        return
    end
    local requestId = unpack_integer4(payload, REQUEST_ID_OFFSET, isLittleEndian)
    messageHandler:messageComplete(messageSize + GIOP_HEADER_SIZE)
    --    print(string.format("request_id=%x", request_id))
    messageHandler:setYahaSessionId(string.format("%x", requestId))
    messageHandler:pushNextLayerRange(0, messageSize + GIOP_HEADER_SIZE)
end


function CorbaMessagePartHandler.processDirectionSwitch(messageHandler)
--[[
Example of direction switch handling, not used by Corba message handler

if messageHandler:direction() == DIRECTION.C2S then
messageHandler:setRequest(true)
else
messageHandler:setResponse(true)
end
local block = messageHandler:currentBlock()
messageHandler:messageComplete(block:length())
messageHandler:pushNextLayerData(BlockBuilder.split(block, 0))
--]]
end


function CorbaMessagePartHandler.trySync(inBlock, outBlock, resyncDirChangedCnt)
    --   amd.print("CorbaMessagePartHandler.trySync")
    local payload = inBlock:c_str()
    if payload:sub(MAGIC_NUMBER_OFFSET, MAGIC_NUMBER_LEN) == GIOP then
        local newPayload = BlockBuilder.split(inBlock, 0);
        outBlock:set(newPayload)
        return true
    end
    return false;
end


-- Parses sequence of Corba messages and decides whether the sequence is complete, detects request.
function CorbaCompleteMessageHandler.parseMessage(messageHandler)
    local current_message_offset = messageHandler:currentMessageOffset()
    --    print("CorbaCompleteMessageHandler.parseMessage: current_message_offset=", current_message_offset)
    local block = messageHandler:currentBlock()
    local payload = block:c_str()
    local fragment = payload:byte(current_message_offset + MESSAGE_FLAGS_OFFSET)
    local isFragment = hasbit(payload:byte(current_message_offset + MESSAGE_FLAGS_OFFSET), bit(2))
    if isFragment then
        messageHandler:needMore(0)
        return
    end
    local messageType = payload:byte(MESSAGE_TYPE_OFFSET)
    local isRequest = (messageType == REQUEST_MESSAGE_TYPE) or (messageType == CANCEL_REQUEST_MESSAGE_TYPE) or (messageType == LOCATE_REQUEST_MESSAGE_TYPE)
    messageHandler:setRequest(isRequest)
    messageHandler:setResponse(not isRequest)
    if not isRequest then
        messageHandler:setLast()
    end
    messageHandler:messageComplete(block:length())
    messageHandler:pushNextLayerRange(0, block:length())
end


function CorbaCompleteMessageHandler.processDirectionSwitch(messageHandler)

end


function CorbaCompleteMessageHandler.trySync(inBlock, outBlock, resyncDirChangedCnt)
    --   print("CorbaCompleteMessageHandler.trySync")
    local payload = inBlock:c_str()
    if payload:sub(MAGIC_NUMBER_OFFSET, MAGIC_NUMBER_LEN) == GIOP then
        local newPayload = BlockBuilder.split(inBlock, 0);
        outBlock:set(newPayload)
        return true
    end
    return false;
end


function parse_request(payload, hit, state)
    local operation_name
    -- 'GIOP' magic word expected:
    if payload:sub(MAGIC_NUMBER_OFFSET, MAGIC_NUMBER_LEN) ~= GIOP then
        operation_name = '<InvalidGIOP>'
        hit:setOperationName(operation_name, operation_name:len())
        amd.print("Not a GIOP message")
        return 1
    end
    local version = unpack_short(payload, VERSION_OFFSET)
    if payload:byte(MESSAGE_TYPE_OFFSET) ~= REQUEST_MESSAGE_TYPE then
        if payload:byte(MESSAGE_TYPE_OFFSET) == LOCATE_REQUEST_MESSAGE_TYPE then
            operation_name = '<Locate>'
            hit:setOperationName(operation_name, operation_name:len())
            return 0
        elseif payload:byte(MESSAGE_TYPE_OFFSET) == FRAGMENT_MESSAGE_TYPE then
            operation_name = '<Fragment>'
            hit:setOperationName(operation_name, operation_name:len())
            return 0
        elseif payload:byte(MESSAGE_TYPE_OFFSET) == CLOSECONNECTION_MESSAGE_TYPE then
            operation_name = '<CloseConnection>'
            hit:setOperationName(operation_name, operation_name:len())
            return 0
        elseif payload:byte(MESSAGE_TYPE_OFFSET) == CANCEL_REQUEST_MESSAGE_TYPE then
            operation_name = '<CancelRequest>'
            hit:setOperationName(operation_name, operation_name:len())
            return 0
        elseif payload:byte(MESSAGE_TYPE_OFFSET) == ERROR_MESSAGE_TYPE then
            operation_name = '<MessageError>'
            hit:setOperationName(operation_name, operation_name:len())
            return 0
        else
            operation_name = string.format('<Unknown0x%x>', payload:byte(MESSAGE_TYPE_OFFSET))
            hit:setOperationName(operation_name, operation_name:len())
            amd.print(string.format('Unknown request message type: 0x%x', payload:byte(MESSAGE_TYPE_OFFSET)))
            return 1
        end
    end
    -- Message Flags: .... ...1 = Little Endian
    local is_little_endian = hasbit(payload:byte(MESSAGE_FLAGS_OFFSET), bit(1))
    hit:setBrowserOsHardware('', version, '', '')

    local keyaddr_length_offset = 1 + GIOP_HEADER_SIZE
    local context = {offset=keyaddr_length_offset}

    if version == GIOP_VERSION_1_1 then
        -- skip servicecontext list:
        consume_servicecontext_list(payload, context, is_little_endian)
        -- calculate 'request_id' field offset,  alignment considered
        calculate_effective_field_offset(context, REQUEST_ID_LEN, GIOP_HEADER_SIZE)
        -- skip 'request_id' field:
        context.offset = context.offset + REQUEST_ID_LEN
        -- skip 'response_expected' field:
        context.offset = context.offset + RESPONSE_EXPECTED_LEN
        -- skip 'reserved' field:
        context.offset = context.offset + RESERVED_LEN
        keyaddr_length_offset = context.offset
    elseif version == GIOP_VERSION_1_2 then
        -- calculate 'request_id' field offset,  alignment considered
        calculate_effective_field_offset(context, REQUEST_ID_LEN, GIOP_HEADER_SIZE)
        -- skip 'request_id' field:
        context.offset = context.offset + REQUEST_ID_LEN
        -- skip 'response_flags' field:
        context.offset = context.offset + RESPONSE_FLAGS_LEN
        -- skip 'reserved' field:
        context.offset = context.offset + RESERVED_LEN
        -- calculate 'target_address' field offset,  alignment considered
        calculate_effective_field_offset(context, TARGET_ADDRESS_LEN, GIOP_HEADER_SIZE)
        -- skip 'target_address' field
        context.offset = context.offset + TARGET_ADDRESS_LEN
        -- calculate 'key_addr_length' field offset,  alignment considered
        keyaddr_length_offset = calculate_effective_field_offset(context, KEYADDR_LENGTH_LEN, GIOP_HEADER_SIZE)
    else
        amd.print(string.format("Unknown GIOP version: 0x%04x", version))
    end

    --	print_hex(payload, keyaddr_length_offset, KEYADDR_LENGTH_LEN)
    local keyaddr_length = unpack_integer4(payload, keyaddr_length_offset, is_little_endian)
    -- skip 'keyaddr_len' field:
    context.offset = context.offset + KEYADDR_LENGTH_LEN
    -- skip key address value:
    context.offset = context.offset + keyaddr_length
    local operation_length_offset = calculate_effective_field_offset(context, OPERATION_LENGTH_LEN, GIOP_HEADER_SIZE)
    -- operation_length includes trailing 0x0 byte
    local operation_length = unpack_integer4(payload, operation_length_offset, is_little_endian)
    --	print('operation_length', operation_length)
    local operation_name_offset = operation_length_offset + OPERATION_LENGTH_LEN
    operation_name = payload:sub(operation_name_offset, operation_name_offset + operation_length - 2)
    hit:setOperationName(operation_name, operation_name:len())
    return 0
end


function parse_response(payload, hit, state)
    -- 'GIOP' magic word expected:
    if payload:sub(MAGIC_NUMBER_OFFSET, MAGIC_NUMBER_LEN) ~= GIOP then
        amd.print('Not a GIOP message')
        return 1
    end
    local version = unpack_short(payload, VERSION_OFFSET)
    if payload:byte(MESSAGE_TYPE_OFFSET) ~= REPLY_MESSAGE_TYPE then
        local operation_name
        if payload:byte(MESSAGE_TYPE_OFFSET) == LOCATE_REPLY_MESSAGE_TYPE then
            operation_name = '<Locate>'
            hit:setOperationName(operation_name, operation_name:len())
            return 0
        elseif payload:byte(MESSAGE_TYPE_OFFSET) == FRAGMENT_MESSAGE_TYPE then
            operation_name = '<Fragment>'
            hit:setOperationName(operation_name, operation_name:len())
            return 0
        elseif payload:byte(MESSAGE_TYPE_OFFSET) == ERROR_MESSAGE_TYPE then
            operation_name = '<MessageError>'
            hit:setOperationName(operation_name, operation_name:len())
            return 0
        else
            amd.print(string.format('Unknown response message type: 0x%x', payload:byte(MESSAGE_TYPE_OFFSET)))
            return 1
        end
    end

    local is_little_endian = hasbit(payload:byte(MESSAGE_FLAGS_OFFSET), bit(1))
    local reply_status_offset = 1 + GIOP_HEADER_SIZE
    local context = {offset=reply_status_offset}
    if version == GIOP_VERSION_1_1 then
        consume_servicecontext_list(payload, context, is_little_endian)
        calculate_effective_field_offset(context, REQUEST_ID_LEN, GIOP_HEADER_SIZE)
        context.offset = context.offset + REQUEST_ID_LEN
        reply_status_offset = context.offset
    elseif version == GIOP_VERSION_1_2 then
        calculate_effective_field_offset(context, REQUEST_ID_LEN, GIOP_HEADER_SIZE)
        context.offset = context.offset + REQUEST_ID_LEN
        reply_status_offset = context.offset
    else
        amd.print(string.format("Unknown GIOP version: 0x%04x", version))
    end

    local reply_status = unpack_integer4(payload, reply_status_offset, is_little_endian)
    if reply_status ~= NO_EXCEPTION then
        if (reply_status == SYSTEM_EXCEPTION) or (reply_status == USER_EXCEPTION) then
            local exception_length_offset = reply_status_offset + REPLY_STATUS_LEN
            context = {offset=exception_length_offset}
            if version == GIOP_VERSION_1_2 then
                consume_servicecontext_list(payload, context, is_little_endian)
                local algmnt_data = {offset=context.offset - GIOP_HEADER_SIZE}
                -- GIOP 1.2 message body must be aligned to 8 octet:
                exception_length_offset = calculate_effective_field_offset(algmnt_data, 8, GIOP_HEADER_SIZE) + GIOP_HEADER_SIZE
            end
            --        amd.print(string.format("exception_length: 0x%02x 0x%02x 0x%02x 0x%02x", payload:byte(exception_length_offset+0), payload:byte(exception_length_offset+1), payload:byte(exception_length_offset+2), payload:byte(exception_length_offset+3)))
            local exception_length = unpack_integer4(payload, exception_length_offset, is_little_endian)
            local exception_id_offset = exception_length_offset + EXCEPTION_LENGTH_LEN
            -- skip trailing 0x0 byte:
            local exception_id = payload:sub(exception_id_offset, exception_id_offset + exception_length - 2)
            hit:setAttribute(1, exception_id)
        else
            hit:setAttribute(2, REPLY_STATUS_TYPE[reply_status] or '<UnknownReplyType>')        
        end
    end

    return 0
end


local the_module = {}
the_module.parse_request = parse_request
the_module.parse_response = parse_response
return the_module
