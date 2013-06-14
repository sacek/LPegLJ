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


-- {======================================================
-- Virtual Machine
-- =======================================================

-- Interpret the result of a dynamic capture: false -> fail;
-- true -> keep current position; number -> next position.
-- Return new subject position. 'fr' is stack index where
-- is the result; 'curr' is current subject position; 'limit'
-- is subject's size.

local ffi = require"ffi"
local lpcap = require"lpcap"
local lpprint = require"lpprint"
local band, rshift, lshift = bit.band, bit.rshift, bit.lshift


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

ffi.cdef[[
  typedef
  struct {
     int p;
     int s;
     int caplevel;
  } STACK;
]]


local function resdyncaptures(fr, curr, limit)
    local typ = type(fr)
    if not fr then -- false value?
        return -1 -- and fail
    elseif typ == 'boolean' then -- true?
        return curr -- keep current position
    else
        local res = fr -- new position
        if res < curr or res > limit then
            error("invalid position returned by match-time capture")
        end
        return res
    end
    assert(false)
end


-- Add capture values returned by a dynamic capture to the capture list
-- 'base', nested inside a group capture. 'fd' indexes the first capture
-- value, 'n' is the number of values (at least 1).

local function adddyncaptures(s, base, index, n, fd)
    -- Cgroup capture is already there
    assert(base[index].kind == Cgroup and base[index].siz == 0)
    base[index].idx = 0 -- make it an anonymous group
    base[index + 1] = {}
    for i = 1, n do -- add runtime captures
        base[index + i].kind = Cruntime
        base[index + i].siz = 1 -- mark it as closed
        base[index + i].idx = fd[i + 1] -- stack index of capture value
        base[index + i].s = s
        base[index + i + 1] = {}
    end
    base[index + n + 1].kind = Cclose -- close group
    base[index + n + 1].siz = 1
    base[index + n + 1].s = s
    base[index + n + 2] = {}
end


-- Opcode interpreter

local function match(o, s, op, capture, ...)
    local STACK = ffi.new("STACK[?]", maxstack)
    local stacklimit = maxstack
    local stackptr = 0 -- point to first empty slot in stack
    local captop = 1 -- point to first empty slot in captures
    capture[captop] = {}

    local p = 1 -- current instruction
    STACK[stackptr].s = s
    STACK[stackptr].caplevel = 0
    STACK[stackptr].p = -1
    stackptr = stackptr + 1

    local function pushcapture()
        capture[captop].idx = op[p].offset
        capture[captop].kind = band(op[p].val, 0x0f)
        captop = captop + 1
        capture[captop] = {}
        p = p + 1
    end

    local function fail()
        -- pattern failed: try to backtrack
        repeat -- remove pending calls
            stackptr = stackptr - 1
            s = STACK[stackptr].s
            until s ~= -1
        captop = STACK[stackptr].caplevel
        for i = #capture, captop + 1, -1 do
            capture[i] = nil
        end
        p = STACK[stackptr].p
    end

    local function doublestack()
        if stackptr >= maxstack then
            error("too many pending calls/choices")
        end
        stacklimit = stacklimit * 2
        stacklimit = (stacklimit > maxstack) and maxstack or stacklimit
        local NEWSTACK = ffi.new("STACK[?]", stacklimit)
        ffi.copy(NEWSTACK, STACK, ffi.sizeof('STACK') * stackptr)
        STACK = NEWSTACK
    end

    while true do
        --[[ Only for debug
                io.write(("s: |%s| stck:%d, caps:%d  \n"):format(s, stackptr, captop))
                if p then
                    lpprint.printinst(op, p)
                    lpprint.printcaplist(capture, captop)
                end
        --]]
        local code = (p >= 0) and op[p].code or IGiveup
        if code == IEnd then
            capture[captop].kind = Cclose
            capture[captop].s = nil
            return s
        elseif code == IGiveup then
            return nil
        elseif code == IRet then
            stackptr = stackptr - 1
            p = STACK[stackptr].p
        elseif code == IAny then
            if s <= o:len() then
                p = p + 1
                s = s + 1
            else
                fail()
            end
        elseif code == ITestAny then
            if s <= o:len() then
                p = p + 1
            else
                p = p + op[p].offset
            end
        elseif code == IChar then
            if s <= o:len() and o:sub(s, s) == op[p].val then
                p = p + 1
                s = s + 1
            else
                fail()
            end
        elseif code == ITestChar then
            if s <= o:len() and o:sub(s, s) == op[p].val then
                p = p + 1
            else
                p = p + op[p].offset
            end
        elseif code == ISet then
            local c = o:sub(s, s):byte()
            if s <= o:len() and band(op[p].val[rshift(c, 5)], lshift(1, band(c, 31))) ~= 0 then
                p = p + 1
                s = s + 1
            else
                fail()
            end
        elseif code == ITestSet then
            local c = o:sub(s, s):byte()
            if s <= o:len() and band(op[p].val[rshift(c, 5)], lshift(1, band(c, 31))) ~= 0 then
                p = p + 1
            else
                p = p + op[p].offset
            end
        elseif code == IBehind then
            local n = op[p].val
            if n >= s then
                fail()
            else
                s = s - n
                p = p + 1
            end
        elseif code == ISpan then
            while s <= o:len() do
                local c = o:sub(s, s):byte()
                if band(op[p].val[rshift(c, 5)], lshift(1, band(c, 31))) == 0 then
                    break
                end
                s = s + 1
            end
            p = p + 1
        elseif code == IJmp then
            p = p + op[p].offset
        elseif code == IChoice then
            if stackptr == stacklimit then
                doublestack()
            end
            STACK[stackptr].p = p + op[p].offset
            STACK[stackptr].s = s
            STACK[stackptr].caplevel = captop
            stackptr = stackptr + 1
            p = p + 1
        elseif code == ICall then
            if stackptr == stacklimit then
                doublestack()
            end
            STACK[stackptr].s = -1
            STACK[stackptr].p = p + 1 -- save return address
            stackptr = stackptr + 1
            p = p + op[p].offset
        elseif code == ICommit then
            stackptr = stackptr - 1
            p = p + op[p].offset
        elseif code == IPartialCommit then
            STACK[stackptr - 1].s = s
            STACK[stackptr - 1].caplevel = captop
            p = p + op[p].offset
        elseif code == IBackCommit then
            stackptr = stackptr - 1
            s = STACK[stackptr].s
            captop = STACK[stackptr].caplevel
            for i = #capture, captop + 1, -1 do
                capture[i] = nil
            end
            p = p + op[p].offset
        elseif code == IFailTwice then
            stackptr = stackptr - 1
            fail()
        elseif code == IFail then
            fail()
        elseif code == ICloseRunTime then
            local cs = {}
            cs.s = o
            cs.ocap = capture
            cs.ptop = { ... }
            cs.ptopcount = select('#', ...)
            local out = { outindex = 0, out = {} }
            local n = lpcap.runtimecap(cs, captop, s, out) -- call function
            for i = 1, n do
                capture[captop] = nil
                captop = captop - 1
            end
            local res = resdyncaptures(out.out[1], s, o:len() + 1) -- get result
            if res == -1 then -- fail?
                fail()
            else
                s = res -- else update current position
                n = out.outindex - 1 -- number of new captures
                if n > 0 then -- any new capture?
                    captop = captop + n + 2
                    -- add new captures to 'capture' list
                    adddyncaptures(s, capture, captop - n - 2, n, out.out)
                end
                p = p + 1
            end
        elseif code == ICloseCapture then
            local s1 = s
            assert(captop > 0)
            -- if possible, turn capture into a full capture
            if capture[captop - 1].siz == 0 and
                    s1 - capture[captop - 1].s < 255 then
                capture[captop - 1].siz = s1 - capture[captop - 1].s + 1
                p = p + 1
            else
                capture[captop].siz = 1 -- mark entry as closed
                capture[captop].s = s
                pushcapture()
            end
        elseif code == IOpenCapture then
            capture[captop].siz = 0 -- mark entry as open
            capture[captop].s = s
            pushcapture()
        elseif code == IFullCapture then
            capture[captop].siz = band(rshift(op[p].val, 4), 0x0F) + 1 -- save capture size
            capture[captop].s = s - band(rshift(op[p].val, 4), 0x0F)
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