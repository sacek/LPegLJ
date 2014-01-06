--[[
LPEGLJ
lpvm.lua
Virtual machine
Copyright (C) 2013 Rostislav Sacek.
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
-- local lpprint = require"lpprint" --only for debug purpose

local band, rshift, lshift = bit.band, bit.rshift, bit.lshift

-- {======================================================
-- Virtual Machine
-- =======================================================

-- Interpret the result of a dynamic capture: false -> fail;
-- true -> keep current position; number -> next position.
-- Return new subject position. 'fr' is stack index where
-- is the result; 'curr' is current subject position; 'limit'
-- is subject's size.

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

local FAIL = -1
local LRFAIL = -1
local VOID = -2

ffi.cdef[[
typedef
struct {
int p;
int s;
int caplevel;
int pA;
int X;
int valuetabletop;
} STACK;

typedef
struct {
int s;
int siz;
int idx;
int kind;
} CAPTURE;
]]


local function resdyncaptures(fr, curr, limit)
    local typ = type(fr)
    if not fr then -- false value?
        return FAIL -- and fail
    elseif typ == 'boolean' then -- true?
        return curr -- keep current position
    else
        local res = fr -- new position
        if res < curr or res > limit then
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

local function match(o, s, op, valuetable, ...)
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
    local maxpointer = 2 ^ math.ceil(math.log(op.size) / math.log(2))

    local p = 0 -- current instruction
    STACK[stackptr].s = s
    STACK[stackptr].p = FAIL
    STACK[stackptr].X = VOID
    stackptr = stackptr + 1

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
            if X ~= VOID then
                s = X
            else
                captop = STACK[stackptr].caplevel
                for i = #valuetable, STACK[stackptr].valuetabletop + 1, -1 do
                    table.remove(valuetable)
                end
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


    while true do
        --[[ Only for debug
        io.write(("s: |%s| stck:%d, caps:%d  \n"):format(s + 1, stackptr, captop))
        if p ~= FAIL then
            lpprint.printinst(op.p, p, valuetable)
            lpprint.printcaplist(CAPTURE, captop, valuetable)
        end
        --]]
        if p == FAIL then return nil end
        local code = op.p[p].code
        if code == IEnd then
            CAPTURE[captop].kind = Cclose
            CAPTURE[captop].s = -1
            return s + 1, CAPTURE
        elseif code == IRet then
            if STACK[stackptr - 1].X == VOID then
                stackptr = stackptr - 1
                p = STACK[stackptr].p
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
        elseif code == IAny then
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
        elseif code == IBehind then
            local n = op.p[p].val
            if n > s then
                fail()
            else
                s = s - n
                p = p + 1
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
            stackptr = stackptr + 1
            p = p + 1
        elseif code == ICall then
            if stackptr == stacklimit then
                doublestack()
            end
            local k = op.p[p].val
            if k == 0 then
                STACK[stackptr].X = VOID
                STACK[stackptr].s = FAIL
                STACK[stackptr].p = p + 1 -- save return address
                stackptr = stackptr + 1
                p = p + op.p[p].offset
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
            local cs = {}
            cs.s = o
            cs.ocap = CAPTURE
            cs.ptop = { ... }
            cs.ptopcount = select('#', ...)
            local out = { outindex = 0, out = {} }
            local n = lpcap.runtimecap(cs, captop, s + 1, out, valuetable) -- call function
            captop = captop - n
            local res = resdyncaptures(out.out[1], s + 1, len + 1) -- get result
            if res == FAIL then -- fail?
                fail()
            else
                s = res - 1 -- else update current position
                n = out.outindex - 1 -- number of new captures
                if n > 0 then -- any new capture?
                    captop = captop + n + 2
                    while captop >= maxcapture do
                        doublecapture()
                    end
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
        else
            assert(false)
        end
    end
end

local function setmax(val)
    maxstack = val
    if maxstack < 100 then
        maxstack = 100
    end
end

-- ======================================================

return {
    match = match,
    setmax = setmax
}
