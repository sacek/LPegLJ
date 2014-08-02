--[[
LPEGLJ
lpvm.lua
Virtual machine
Copyright (C) 2014 Rostislav Sacek.
based on LPeg v0.12 - PEG pattern matching for Lua
Lua.org & PUC-Rio  written by Roberto Ierusalimschy
http://www.inf.puc-rio.br/~roberto/lpeg/

** Permission is hereby granted, free of charge, to any person obtaining
** a copy of this software and associated documentation files (the
** "Software"), to deal in the Software without restriction, including
** without limitation the rights to use, copy, modify, merge, publish,
** distribute, sublicense, and/or sell copies of the Software, and to
** permit persons to whom the Software is furnished to do so, subject to
** the following conditions:
**
** The above copyright notice and this permission notice shall be
** included in all copies or substantial portions of the Software.
**
** THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
** EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
** MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
** IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
** CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
** TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
** SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**
** [ MIT license: http://www.opensource.org/licenses/mit-license.php ]
--]]

local ffi = require"ffi"
local lpcap = require"lpcap"
local lpprint = require"lpprint" --only for debug purpose

local band, rshift, lshift = bit.band, bit.rshift, bit.lshift

-- {======================================================
-- Virtual Machine
-- =======================================================

-- Interpret the result of a dynamic capture: false -> fail;
-- true -> keep current position; number -> next position.
-- Return new subject position. 'fr' is stack index where
-- is the result; 'curr' is current subject position; 'limit'
-- is subject's size.

local MAXBEHINDPREDICATE = 255 -- max behind for Look-behind predicate
local MAXOFF = 0xF -- maximum for full capture
local MAXBEHIND = math.max(MAXBEHINDPREDICATE, MAXOFF) -- maximum before current pos

local IAny = 0 -- if no char, fail
local IChar = 1 -- if char != val, fail
local ISet = 2 -- if char not in val, fail
local ITestAny = 3 -- in no char, jump to 'offset'
local ITestChar = 4 -- if char != val, jump to 'offset'
local ITestSet = 5 -- if char not in val, jump to 'offset'
local ISpan = 6 -- read a span of chars in val
local IBehind = 7 -- walk back 'val' characters (fail if not possible)
local IRet = 8 -- return from a rule
local IEnd = 9 -- end of pattern
local IChoice = 10 -- stack a choice; next fail will jump to 'offset'
local IJmp = 11 -- jump to 'offset'
local ICall = 12 -- call rule at 'offset'
local IOpenCall = 13 -- call rule number 'offset' (must be closed to a ICall)
local ICommit = 14 -- pop choice and jump to 'offset'
local IPartialCommit = 15 -- update top choice to current position and jump
local IBackCommit = 16 -- "fails" but jump to its own 'offset'
local IFailTwice = 17 -- pop one choice and then fail
local IFail = 18 -- go back to saved state on choice and jump to saved offset
local IGiveup = 19 -- internal use
local IFullCapture = 20 -- complete capture of last 'off' chars
local IOpenCapture = 21 -- start a capture
local ICloseCapture = 22
local ICloseRunTime = 23

local Cclose = 0
local Cposition = 1
local Cconst = 2
local Cbackref = 3
local Carg = 4
local Csimple = 5
local Ctable = 6
local Cfunction = 7
local Cquery = 8
local Cstring = 9
local Cnum = 10
local Csubst = 11
local Cfold = 12
local Cruntime = 13
local Cgroup = 14

local maxstack = 100
local maxcapturedefault = 100
local maxmemo = 1000
local usememoization = false

local FAIL = -1
local LRFAIL = -1
local VOID = -2

ffi.cdef[[
typedef
struct {
int p;
double s;
int caplevel;
int pA;
double X;
int valuetabletop;
double memos;
int call;
} STACK;

typedef
struct {
double s;
int siz;
int idx;
int kind;
} CAPTURE;
]]


local function resdyncaptures(fr, curr, limit, checkstreamlen)
    local typ = type(fr)
    if not fr then -- false value?
        return FAIL -- and fail
    elseif typ == 'boolean' then -- true?
        return curr -- keep current position
    else
        local res = fr -- new position
        if res < curr or (limit and res > limit) or (not limit and checkstreamlen and not checkstreamlen(res - 2)) then
            error("invalid position returned by match-time capture", 0)
        end
        return res
    end
    assert(false)
end


-- Add capture values returned by a dynamic capture to the capture list
-- 'base', nested inside a group capture. 'fd' indexes the first capture
-- value, 'n' is the number of values (at least 1).

local function adddyncaptures(s, base, index, n, fd, valuetable)
    -- Cgroup capture is already there
    assert(base[index].kind == Cgroup and base[index].siz == 0)
    local ind = #valuetable + 1
    valuetable[ind] = 0
    base[index].idx = ind -- make it an anonymous group
    base[index + 1] = {}
    for i = 1, n do -- add runtime captures
        base[index + i].kind = Cruntime
        base[index + i].siz = 1 -- mark it as closed
        ind = #valuetable + 1
        valuetable[ind] = fd[i + 1]
        base[index + i].idx = ind -- stack index of capture value
        base[index + i].s = s
        base[index + i + 1] = {}
    end
    base[index + n + 1].kind = Cclose -- close group
    base[index + n + 1].siz = 1
    base[index + n + 1].s = s
    base[index + n + 2] = {}
end


-- Opcode interpreter

local function match(stream, last, o, s, op, valuetable, ...)
    local arg = { ... }
    local argcount = select('#', ...)
    local len = #o
    local ptr = ffi.cast('const unsigned char*', o)
    s = s - 1
    local stackptr = 0 -- point to first empty slot in stack
    local captop = 0 -- point to first empty slot in captures
    local STACK = ffi.new("STACK[?]", maxstack)
    local CAPTURE = ffi.new("CAPTURE[?]", maxcapturedefault)
    local CAPTURESTACK = { { capture = CAPTURE, captop = captop, maxcapture = maxcapturedefault } }
    local capturestackptr = #CAPTURESTACK
    local maxcapture = maxcapturedefault
    local stacklimit = maxstack
    local L = {}
    local Memo1, Memo2 = {}, {}
    local memoind = 0
    local maxpointer = 2 ^ math.ceil(math.log(op.size) / math.log(2))

    local p = 0 -- current instruction
    STACK[stackptr].s = VOID
    STACK[stackptr].p = FAIL
    STACK[stackptr].X = VOID
    STACK[stackptr].memos = VOID
    STACK[stackptr].call = 0
    stackptr = stackptr + 1

    local streambufsize = 2 ^ 8
    local streambufsizemask = streambufsize - 1 -- faster modulo
    local streambufs = {}
    local streambufoffset = 0
    local streamstartbuffer = 0
    local streambufferscount = 0

    local function deletestreambuffers()
        local min = s
        for i = stackptr - 1, 1, -1 do
            local val = STACK[i].s
            if val >= 0 then
                min = math.min(val, min)
            end
        end

        for i = captop - 1, 0, -1 do
            local val = CAPTURE[i].s
            if val >= 0 then
                min = math.min(val, min)
            end
        end
        for i = streamstartbuffer + 1, streambufoffset - streambufsize, streambufsize do
            if i + streambufsize + MAXBEHIND < min then -- max behind for full capture and max behind for Look-behind predicate
                streambufs[i] = nil
                streambufferscount = streambufferscount - 1
            else
                streamstartbuffer = i - 1
                break
            end
        end
    end

    local function addstreamdata(s, last)
        local len = #s
        local srcoffset = 0
        if streambufferscount > 128 then
            deletestreambuffers()
        end
        repeat
            local offset = bit.band(streambufoffset, streambufsizemask)
            if offset > 0 then
                local index = streambufoffset - offset + 1
                local count = math.min(len, streambufsize - offset)
                ffi.copy(streambufs[index] + offset, s:sub(srcoffset + 1, srcoffset + 1 + count), count)
                len = len - count
                srcoffset = srcoffset + count
                streambufoffset = streambufoffset + count
            end
            if len > 0 then
                local index = streambufoffset - (bit.band(streambufoffset, streambufsizemask)) + 1
                local buf = ffi.new('unsigned char[?]', streambufsize)
                streambufferscount = streambufferscount + 1
                streambufs[index] = buf
                local count = math.min(len, streambufsize)
                ffi.copy(buf, s:sub(srcoffset + 1, srcoffset + 1 + count), count)
                len = len - count
                srcoffset = srcoffset + count
                streambufoffset = streambufoffset + count
            end
            if streambufoffset >= 2 ^ 47 then
                error("too big input stream", 0)
            end
        until len == 0
    end

    local function getstreamchar(s)
        local offset = bit.band(s, streambufsizemask)
        local index = s - offset + 1
        return streambufs[index][offset]
    end

    local checkstreamlen

    local function getstreamstring(st, en) -- TODO Optimalize access
        local str = {}
        local i = st >= 0 and st or 1
        local to = en >= 0 and en or math.huge
        while true do
            if i > to then break end
            checkstreamlen(i - 1)
            if last and (st < 0 or en < 0) then
                for j = i, streambufoffset do
                    str[#str + 1] = string.char(getstreamchar(j - 1))
                end
                en = en < 0 and streambufoffset + en + 1 or en
                en = st > 0 and en - st + 1 or en
                st = st < 0 and streambufoffset + st + 1 or 1
                return table.concat(str):sub(st, en)
            else
                str[#str + 1] = string.char(getstreamchar(i - 1))
                i = i + 1
            end
        end
        return table.concat(str)
    end

    function checkstreamlen(index)
        local str
        while true do
            if index < streambufoffset then
                return true
            else
                if last then
                    s = streambufoffset
                    return false
                end

                local min = captop
                for i = stackptr - 1, 1, -1 do
                    local val = STACK[i].call == 0 and STACK[i].caplevel or -1
                    if val >= 0 then
                        min = math.min(val, min)
                    end
                end
                local n, out, outindex = lpcap.getcapturesruntime(CAPTURE, getstreamstring, min, valuetable, unpack(arg, 1, argcount))
                if n > 0 then
                    for i = 0, captop - n do
                        ffi.copy(CAPTURE + i, CAPTURE + i + n, ffi.sizeof('CAPTURE'))
                    end

                    for i = stackptr - 1, 1, -1 do
                        local val = STACK[i].caplevel
                        if val >= 0 then
                            STACK[i].caplevel = STACK[i].caplevel - n
                        end
                    end
                    captop = captop - n
                end
                str, last = coroutine.yield(1, unpack(out, 1, outindex))
                addstreamdata(str)
            end
        end
    end

    local function doublecapture()
        maxcapture = maxcapture * 2
        local NEWCAPTURE = ffi.new("CAPTURE[?]", maxcapture)
        ffi.copy(NEWCAPTURE, CAPTURE, ffi.sizeof('CAPTURE') * captop)
        CAPTURE = NEWCAPTURE
        CAPTURESTACK[capturestackptr].capture = CAPTURE
        CAPTURESTACK[capturestackptr].maxcapture = maxcapture
    end

    local function pushcapture()
        CAPTURE[captop].idx = op.p[p].offset
        CAPTURE[captop].kind = band(op.p[p].val, 0x0f)
        captop = captop + 1
        p = p + 1
        if captop >= maxcapture then
            doublecapture()
        end
    end

    local function fail()
        -- pattern failed: try to backtrack
        local X
        repeat -- remove pending calls
            stackptr = stackptr - 1
            s = STACK[stackptr].s
            X = STACK[stackptr].X
            if usememoization and s == FAIL and STACK[stackptr].memos ~= VOID then
                Memo1[STACK[stackptr].pA + STACK[stackptr].memos * maxpointer] = FAIL
                Memo2[STACK[stackptr].pA + STACK[stackptr].memos * maxpointer] = FAIL
            end
            if X == LRFAIL then
                CAPTURESTACK[capturestackptr] = nil
                capturestackptr = capturestackptr - 1
                CAPTURE = CAPTURESTACK[capturestackptr].capture
                maxcapture = CAPTURESTACK[capturestackptr].maxcapture
                L[STACK[stackptr].pA + s * maxpointer] = nil
            end
        until s ~= FAIL and X ~= LRFAIL
        p = STACK[stackptr].p
        if p ~= FAIL then
            for i = #valuetable, STACK[stackptr].valuetabletop + 1, -1 do
                table.remove(valuetable)
            end
            if X ~= VOID then
                s = X
                capturestackptr = capturestackptr - 1
                CAPTURE = CAPTURESTACK[capturestackptr].capture
                captop = CAPTURESTACK[capturestackptr].captop
                maxcapture = CAPTURESTACK[capturestackptr].maxcapture
                local capture = L[STACK[stackptr].pA + STACK[stackptr].s * maxpointer].capturecommit
                while captop + capture.captop >= maxcapture do
                    doublecapture()
                end
                ffi.copy(CAPTURE + captop, capture.capture, capture.captop * ffi.sizeof('CAPTURE'))
                captop = captop + capture.captop
                CAPTURESTACK[capturestackptr + 1] = nil
                L[STACK[stackptr].pA + STACK[stackptr].s * maxpointer] = nil
            else
                captop = STACK[stackptr].caplevel
            end
        end
    end

    local function doublestack()
        if stackptr >= maxstack then
            error("too many pending calls/choices", 0)
        end
        stacklimit = stacklimit * 2
        stacklimit = (stacklimit > maxstack) and maxstack or stacklimit
        local NEWSTACK = ffi.new("STACK[?]", stacklimit)
        ffi.copy(NEWSTACK, STACK, ffi.sizeof('STACK') * stackptr)
        STACK = NEWSTACK
    end

    if stream then
        addstreamdata(o)
        len = nil
        o = nil
        ptr = nil
    end
    while true do
        --[[ Only for debug
        io.write(("s: |%s| stck:%d, caps:%d  \n"):format(s + 1, stackptr, captop))
        if p ~= FAIL then
            lpprint.printinst(op.p, p, valuetable)
            lpprint.printcaplist(CAPTURE, captop, valuetable)
        end
        --]]
        if p == FAIL then return -1 end
        local code = op.p[p].code
        if code == IEnd then
            CAPTURE[captop].kind = Cclose
            CAPTURE[captop].s = -1
            return 0, lpcap.getcaptures(CAPTURE, o, getstreamstring, s + 1, valuetable, ...)
        elseif code == IRet then
            if STACK[stackptr - 1].X == VOID then
                stackptr = stackptr - 1
                p = STACK[stackptr].p
                if usememoization and STACK[stackptr].memos ~= VOID then
                    local dif = captop - STACK[stackptr].caplevel
                    local caps
                    if dif > 0 then
                        caps = ffi.new("CAPTURE[?]", dif)
                        ffi.copy(caps, CAPTURE + captop - dif, dif * ffi.sizeof('CAPTURE'))
                    end
                    local val = { s, dif, caps }
                    Memo1[STACK[stackptr].pA + STACK[stackptr].memos * maxpointer] = val
                    Memo2[STACK[stackptr].pA + STACK[stackptr].memos * maxpointer] = val
                end
            else
                local X = STACK[stackptr - 1].X
                if X == LRFAIL or s > X then
                    STACK[stackptr - 1].X = s
                    p = STACK[stackptr - 1].pA
                    s = STACK[stackptr - 1].s
                    local lambda = L[p + s * maxpointer]
                    lambda.X = STACK[stackptr - 1].X
                    STACK[stackptr - 1].caplevel = captop
                    STACK[stackptr - 1].valuetabletop = #valuetable
                    CAPTURESTACK[capturestackptr].captop = captop
                    lambda.capturecommit = CAPTURESTACK[capturestackptr]
                    captop = 0
                    CAPTURE = ffi.new("CAPTURE[?]", maxcapturedefault)
                    CAPTURESTACK[capturestackptr] = { capture = CAPTURE, captop = captop, maxcapture = maxcapturedefault }
                    maxcapture = maxcapturedefault
                else
                    stackptr = stackptr - 1
                    p = STACK[stackptr].p
                    s = STACK[stackptr].X
                    for i = #valuetable, STACK[stackptr].valuetabletop + 1, -1 do
                        table.remove(valuetable)
                    end
                    local lambda = L[STACK[stackptr].pA + STACK[stackptr].s * maxpointer]
                    capturestackptr = capturestackptr - 1
                    CAPTURE = CAPTURESTACK[capturestackptr].capture
                    captop = CAPTURESTACK[capturestackptr].captop
                    maxcapture = CAPTURESTACK[capturestackptr].maxcapture
                    local capture = lambda.capturecommit
                    while captop + capture.captop >= maxcapture do
                        doublecapture()
                    end
                    ffi.copy(CAPTURE + captop, capture.capture, capture.captop * ffi.sizeof('CAPTURE'))
                    captop = captop + capture.captop
                    CAPTURESTACK[capturestackptr + 1] = nil
                    L[STACK[stackptr].pA + STACK[stackptr].s * maxpointer] = nil
                end
            end
        elseif code == IBehind then
            local n = op.p[p].val
            if n > s then
                fail()
            else
                s = s - n
                p = p + 1
            end
        elseif code == IJmp then
            p = p + op.p[p].offset
        elseif code == IChoice then
            if stackptr == stacklimit then
                doublestack()
            end
            STACK[stackptr].X = VOID
            STACK[stackptr].p = p + op.p[p].offset
            STACK[stackptr].s = s
            STACK[stackptr].caplevel = captop
            STACK[stackptr].valuetabletop = #valuetable
            STACK[stackptr].call = 0
            stackptr = stackptr + 1
            p = p + 1
        elseif code == ICall then
            if stackptr == stacklimit then
                doublestack()
            end
            local k = bit.band(op.p[p].val, 0xffff)
            if k == 0 then
                local pA = p + op.p[p].offset
                local memo = Memo1[pA + s * maxpointer]
                if usememoization and memo and type(memo) == 'table' then
                    s = memo[1]
                    local dif = memo[2]
                    if dif > 0 then
                        while captop + dif >= maxcapture do
                            doublecapture()
                        end
                        local caps = memo[3]
                        ffi.copy(CAPTURE + captop, caps, dif * ffi.sizeof('CAPTURE'))
                        captop = captop + dif
                    end
                    p = p + 1
                else
                    STACK[stackptr].X = VOID
                    STACK[stackptr].s = FAIL
                    STACK[stackptr].p = p + 1 -- save return address
                    STACK[stackptr].pA = pA
                    STACK[stackptr].memos = s
                    STACK[stackptr].caplevel = captop
                    STACK[stackptr].call = 1
                    stackptr = stackptr + 1
                    p = pA
                    if usememoization then
                        if not memo then
                            memoind = memoind + 1
                            if memoind > maxmemo then
                                memoind = 0
                                Memo1 = Memo2
                                Memo2 = {}
                            end
                        elseif memo == FAIL then
                            fail()
                        end
                    end
                end
            else
                local pA = p + op.p[p].offset
                local X = L[pA + s * maxpointer]
                if not X then
                    CAPTURESTACK[capturestackptr].captop = captop
                    local capture = ffi.new("CAPTURE[?]", maxcapturedefault)
                    capturestackptr = capturestackptr + 1
                    CAPTURESTACK[capturestackptr] = { capture = capture, captop = captop, maxcapture = maxcapturedefault }
                    CAPTURE = capture
                    maxcapture = maxcapturedefault
                    captop = 0
                    L[pA + s * maxpointer] = { X = LRFAIL, k = k, cs = capturestackptr }
                    STACK[stackptr].p = p + 1
                    STACK[stackptr].pA = pA
                    STACK[stackptr].s = s
                    STACK[stackptr].X = LRFAIL
                    STACK[stackptr].call = 0
                    stackptr = stackptr + 1
                    p = pA
                elseif X.X == LRFAIL or k < X.k then
                    fail()
                else
                    local capture = X.capturecommit
                    while captop + capture.captop >= maxcapture do
                        doublecapture()
                    end
                    ffi.copy(CAPTURE + captop, capture.capture, capture.captop * ffi.sizeof('CAPTURE'))
                    captop = captop + capture.captop
                    p = p + 1
                    s = X.X
                end
            end
        elseif code == ICommit then
            stackptr = stackptr - 1
            p = p + op.p[p].offset
        elseif code == IPartialCommit then
            STACK[stackptr - 1].s = s
            STACK[stackptr - 1].caplevel = captop
            STACK[stackptr - 1].valuetabletop = #valuetable
            p = p + op.p[p].offset
        elseif code == IBackCommit then
            stackptr = stackptr - 1
            s = STACK[stackptr].s
            captop = STACK[stackptr].caplevel
            for i = #valuetable, STACK[stackptr].valuetabletop + 1, -1 do
                table.remove(valuetable)
            end
            p = p + op.p[p].offset
        elseif code == IFailTwice then
            stackptr = stackptr - 1
            fail()
        elseif code == IFail then
            fail()
        elseif code == ICloseRunTime then
            for i = 0, stackptr - 1 do -- invalidate memo
                STACK[i].memos = VOID
            end
            local cs = {}
            cs.s = o
            cs.stream = getstreamstring
            cs.ocap = CAPTURE
            cs.ptop = arg
            cs.ptopcount = argcount
            local out = { outindex = 0, out = {} }
            local n = lpcap.runtimecap(cs, captop, s + 1, out, valuetable) -- call function
            captop = captop - n
            local res = resdyncaptures(out.out[1], s + 1, len and len + 1, checkstreamlen) -- get result
            if res == FAIL then -- fail?
                fail()
            else
                s = res - 1 -- else update current position
                n = out.outindex - 1 -- number of new captures
                if n > 0 then -- any new capture?
                    captop = captop + 1
                    while captop + n + 1 >= maxcapture do
                        doublecapture()
                    end
                    captop = captop + n + 1
                    -- add new captures to 'capture' list
                    adddyncaptures(s + 1, CAPTURE, captop - n - 2, n, out.out, valuetable)
                end
                p = p + 1
            end
        elseif code == ICloseCapture then
            local s1 = s + 1
            assert(captop > 0)
            -- if possible, turn capture into a full capture
            if CAPTURE[captop - 1].siz == 0 and
                    s1 - CAPTURE[captop - 1].s < 255 then
                CAPTURE[captop - 1].siz = s1 - CAPTURE[captop - 1].s + 1
                p = p + 1
            else
                CAPTURE[captop].siz = 1
                CAPTURE[captop].s = s + 1
                pushcapture()
            end
        elseif code == IOpenCapture then
            CAPTURE[captop].siz = 0
            CAPTURE[captop].s = s + 1
            pushcapture()
        elseif code == IFullCapture then
            CAPTURE[captop].siz = band(rshift(op.p[p].val, 4), 0x0F) + 1 -- save capture size
            CAPTURE[captop].s = s + 1 - band(rshift(op.p[p].val, 4), 0x0F)
            pushcapture()
        elseif o then -- standard mode
            if code == IAny then
                if s < len then
                    p = p + 1
                    s = s + 1
                else
                    fail()
                end
            elseif code == ITestAny then
                if s < len then
                    p = p + 1
                else
                    p = p + op.p[p].offset
                end
            elseif code == IChar then
                if s < len and ptr[s] == op.p[p].val then
                    p = p + 1
                    s = s + 1
                else
                    fail()
                end
            elseif code == ITestChar then
                if s < len and ptr[s] == op.p[p].val then
                    p = p + 1
                else
                    p = p + op.p[p].offset
                end
            elseif code == ISet then
                local c = ptr[s]
                local set = valuetable[op.p[p].val]
                if s < len and band(set[rshift(c, 5)], lshift(1, band(c, 31))) ~= 0 then
                    p = p + 1
                    s = s + 1
                else
                    fail()
                end
            elseif code == ITestSet then
                local c = ptr[s]
                local set = valuetable[op.p[p].val]
                if s < len and band(set[rshift(c, 5)], lshift(1, band(c, 31))) ~= 0 then
                    p = p + 1
                else
                    p = p + op.p[p].offset
                end
            elseif code == ISpan then
                while s < len do
                    local c = ptr[s]
                    local set = valuetable[op.p[p].val]
                    if band(set[rshift(c, 5)], lshift(1, band(c, 31))) == 0 then
                        break
                    end
                    s = s + 1
                end
                p = p + 1
            end
        else -- stream mode
            if code == IAny then
                if checkstreamlen(s) then
                    p = p + 1
                    s = s + 1
                else
                    fail()
                end
            elseif code == ITestAny then
                if checkstreamlen(s) then
                    p = p + 1
                else
                    p = p + op.p[p].offset
                end
            elseif code == IChar then
                if checkstreamlen(s) and getstreamchar(s) == op.p[p].val then
                    p = p + 1
                    s = s + 1
                else
                    fail()
                end
            elseif code == ITestChar then
                if checkstreamlen(s) and getstreamchar(s) == op.p[p].val then
                    p = p + 1
                else
                    p = p + op.p[p].offset
                end
            elseif code == ISet then
                local c = checkstreamlen(s) and getstreamchar(s)
                local set = valuetable[op.p[p].val]
                if c and band(set[rshift(c, 5)], lshift(1, band(c, 31))) ~= 0 then
                    p = p + 1
                    s = s + 1
                else
                    fail()
                end
            elseif code == ITestSet then
                local c = checkstreamlen(s) and getstreamchar(s)
                local set = valuetable[op.p[p].val]
                if c and band(set[rshift(c, 5)], lshift(1, band(c, 31))) ~= 0 then
                    p = p + 1
                else
                    p = p + op.p[p].offset
                end
            elseif code == ISpan then
                while checkstreamlen(s) do
                    local c = getstreamchar(s)
                    local set = valuetable[op.p[p].val]
                    if band(set[rshift(c, 5)], lshift(1, band(c, 31))) == 0 then
                        break
                    end
                    s = s + 1
                end
                p = p + 1
            end
        end
    end
end

local function setmax(val)
    maxstack = val
    if maxstack < 100 then
        maxstack = 100
    end
end

local function setmaxbehind(val)
    MAXBEHIND = math.max(MAXBEHINDPREDICATE, MAXOFF, val or 0)
end

local function enablememoization(val)
    usememoization = val
end

-- ======================================================

return {
    match = match,
    setmax = setmax,
    setmaxbehind = setmaxbehind,
    enablememoization = enablememoization
}
