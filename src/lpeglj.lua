--[[
LPEGLJ
lpeglj.lua
Main module and tree generation
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
local lpcode = require"lpcode"
local lpprint = require"lpprint"
local lpvm = require"lpvm"
local lpcap = require"lpcap"

local band, bor, bnot, rshift, lshift = bit.band, bit.bor, bit.bnot, bit.rshift, bit.lshift

ffi.cdef[[
 int isalnum(int c);
 int isalpha(int c);
 int iscntrl(int c);
 int isdigit(int c);
 int isgraph(int c);
 int islower(int c);
 int isprint(int c);
 int ispunct(int c);
 int isspace(int c);
 int isupper(int c);
 int isxdigit(int c);
]]


local MAXBEHIND = 255
local MAXRULES = 200
local VERSION = "0.12LJ"

local TChar = 0
local TSet = 1
local TAny = 2 -- standard PEG elements
local TTrue = 3
local TFalse = 4
local TRep = 5
local TSeq = 6
local TChoice = 7
local TNot = 8
local TAnd = 9
local TCall = 10
local TOpenCall = 11
local TRule = 12 -- sib1 is rule's pattern, sib2 is 'next' rule
local TGrammar = 13 -- sib1 is initial (and first) rule
local TBehind = 14 -- match behind
local TCapture = 15 -- regular capture
local TRunTime = 16 -- run-time capture

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

local PEnullable = 0
local PEnofail = 1

local newgrammar
local metareg
local maketree
local get_concrete_tree


-- number of siblings for each tree
local numsiblings = {
    0, 0, 0, -- char, set, any
    0, 0, -- true, false
    1, -- rep
    2, 2, -- seq, choice
    1, 1, -- not, and
    0, 0, 2, 1, -- call, opencall, rule, grammar
    1, -- behind
    1, 1 -- capture, runtime capture
}

local function copy(t1, t2)
    t1.tag = t2.tag
    t1.val = t2.val
    t1.ps = t2.ps
    t1.cap = t2.cap
end

-- Fix a TOpenCall into a TCall node, using table 'postable' to
-- translate a key to its rule address in the tree. Raises an
-- error if key does not exist.

local function fixonecall(postable, grammar, index)
    local name = grammar[index].val -- get rule's name
    local n = postable[name] -- query name in position table
    if not n then -- no position?
        error(("rule '%s' undefined in given grammar"):format(type(name) == 'table' and '(a table)' or name))
    end
    grammar[index].tag = TCall;
    grammar[index].ps = n - index + 1 -- position relative to node
    assert(grammar[index + grammar[index].ps].tag == TRule)
    grammar[index + grammar[index].ps].val = grammar[index].val
end


-- Transform left associative constructions into right
-- associative ones, for sequence and choice; that is:
-- (t11 + t12) + t2  =>  t11 + (t12 + t2)
-- (t11 * t12) * t2  =>  t11 * (t12 * t2)
-- (that is, Op (Op t11 t12) t2 => Op t11 (Op t12 t2))

local function correctassociativity(tree, index)
    local t1 = index + 1
    assert(tree[index].tag == TChoice or tree[index].tag == TSeq)
    while tree[t1].tag == tree[index].tag do
        local n1size = tree[index].ps - 1; -- t1 == Op t11 t12
        local n11size = tree[t1].ps - 1;
        local n12size = n1size - n11size - 1
        for i = 1, n11size do
            copy(tree[index + i], tree[t1 + i])
        end
        tree[index].ps = n11size + 1
        tree[index + tree[index].ps].tag = tree[index].tag
        tree[index + tree[index].ps].ps = n12size + 1
    end
end


-- Make final adjustments in a tree. Fix open calls in tree 't',
-- making them refer to their respective rules or raising appropriate
-- errors (if not inside a grammar). Correct associativity of associative
-- constructions (making them right associative). Assume that tree's
-- ktable is at the top of the stack (for error messages).

local function finalfix(fix, postable, grammar, index)

    local tag = grammar[index].tag
    if tag == TGrammar then --subgrammars were already fixed
        return
    elseif tag == TOpenCall then
        if fix then -- inside a grammar?
            fixonecall(postable, grammar, index)
        else -- open call outside grammar
            error(("rule '%s' used outside a grammar"):format(tostring(grammar[index].val)))
        end
    elseif tag == TSeq or tag == TChoice then
        correctassociativity(grammar, index)
    end
    local ns = numsiblings[tag + 1]
    if ns == 0 then
    elseif ns == 1 then
        return finalfix(fix, postable, grammar, index + 1)
    elseif ns == 2 then
        finalfix(fix, postable, grammar, index + 1)
        return finalfix(fix, postable, grammar, index + grammar[index].ps)
    else
        assert(false)
    end
end


-- {======================================================
-- Tree generation
-- =======================================================

local function gettree(val)
    if getmetatable(val) == metareg then
        return val
    end
end


-- create a pattern

local function newtree(len)
    local tree = {}
    tree.code = nil
    tree.size = len
    for i = 1, len do
        tree[i] = {}
    end
    return maketree(tree)
end


local function newleaf(tag)
    local tree = newtree(1)
    tree[1].tag = tag;
    return tree
end


local function newcharset()
    local tree = newtree(1)
    tree[1].tag = TSet
    tree[1].val = ffi.new('uint32_t[8]')
    return tree;
end


-- add to tree a sequence where first sibling is 'sib' (with size
-- 'sibsize'); returns position for second sibling

local function seqaux(tree, sib, start, sibsize)
    tree[start].tag = TSeq;
    tree[start].ps = sibsize + 1
    for i = 1, sibsize do
        copy(tree[start + i], sib[i])
    end
end


-- Build a sequence of 'n' nodes, each with tag 'tag' and 'u.n' got
-- from the array 's' (or 0 if array is NULL). (TSeq is binary, so it
-- must build a sequence of sequence of sequence...)

local function fillseq(tree, tag, start, n, s)
    for i = 1, n - 1 do -- initial n-1 copies of Seq tag; Seq ...
        tree[start].tag = TSeq
        tree[start].ps = 2
        tree[start + 1].tag = tag
        tree[start + 1].val = s and s:sub(i, i)
        start = start + tree[start].ps
    end
    tree[start].tag = tag -- last one does not need TSeq
    tree[start].val = s and s:sub(n, n)
end


-- Numbers as patterns:
-- 0 == true (always match); n == TAny repeated 'n' times;
-- -n == not (TAny repeated 'n' times)

local function numtree(n)
    if n == 0 then
        return newleaf(TTrue)
    else
        local tree, start
        if n > 0 then
            tree = newtree(2 * n - 1)
            start = 1
        else -- negative: code it as !(-n)
            n = -n;
            tree = newtree(2 * n)
            tree[1].tag = TNot;
            start = 2
        end
        fillseq(tree, TAny, start, n, nil) -- sequence of 'n' any's
        return tree;
    end
end


-- Convert value to a pattern

local function getpatt(val)
    local tree = gettree(val)
    local type = type(val)

    if tree then
        return tree
    elseif type == 'string' then
        if #val == 0 then -- empty?
            tree = newleaf(TTrue) -- always match
        else
            tree = newtree(2 * (#val - 1) + 1)
            fillseq(tree, TChar, 1, #val, val) -- sequence of 'slen' chars
        end
    elseif type == 'number' then
        tree = numtree(val)
    elseif type == 'boolean' then
        tree = val and newleaf(TTrue) or newleaf(TFalse)
    elseif type == 'table' then
        tree = newgrammar(val)
    elseif type == 'function' then
        tree = newtree(2)
        tree[1].tag = TRunTime;
        tree[1].val = val
        tree[2].tag = TTrue
    end
    return tree;
end


-- create a new tree, whith a new root and one sibling.
-- Sibling must be on the Lua stack, at index 1.

local function newroot1sib(tag, pat)
    local tree1 = getpatt(pat)
    local tree = newtree(1 + tree1.size) -- create new tree
    tree[1].tag = tag;
    for i = 1, tree1.size do
        copy(tree[i + 1], tree1[i])
    end
    return tree;
end


-- create a new tree, with a new root and 2 siblings.
-- Siblings must be on the Lua stack, first one at index 1.

local function newroot2sib(tag, pat1, pat2)
    local tree1 = getpatt(pat1)
    local tree2 = getpatt(pat2)
    local tree = newtree(1 + tree1.size + tree2.size) -- create new tree
    tree[1].tag = tag;
    tree[1].ps = 1 + tree1.size
    for i = 1, tree1.size do
        copy(tree[1 + i], tree1[i])
    end
    for i = 1, tree2.size do
        copy(tree[tree[1].ps + i], tree2[i])
    end
    return tree;
end


local function lp_P(par)
    assert(select('#', par) > 0)
    return getpatt(par)
end


-- sequence operator; optimizations:
-- false x => false, x true => x, true x => x
-- (cannot do x . false => false because x may have runtime captures)

local function lp_seq(pat1, pat2)
    local tree1 = getpatt(pat1)
    local tree2 = getpatt(pat2)
    if tree1[1].tag == TFalse or tree2[1].tag == TTrue then --  false . x == false, x . true = x
        return tree1
    elseif tree1[1].tag == TTrue then -- true . x = x
        return tree2
    else
        return newroot2sib(TSeq, tree1, tree2)
    end
end


-- choice operator; optimizations:
-- charset / charset => charset
-- true / x => true, x / false => x, false / x => x
-- (x / true is not equivalent to true)

local function lp_choice(pat1, pat2)
    local tree1 = getpatt(pat1)
    local tree2 = getpatt(pat2)
    local charset1 = lpcode.tocharset(tree1, 1)
    local charset2 = lpcode.tocharset(tree2, 1)
    if charset1 and charset2 then
        local t = newcharset()
        for i = 0, 7 do
            t[1].val[i] = bor(charset1[i], charset2[i])
        end
        return t
    elseif lpcode.checkaux(tree1, PEnofail, 1) or tree2[1].tag == TFalse then
        return tree1 -- true / x => true, x / false => x
    elseif tree1[1].tag == TFalse then
        return tree2 -- false / x => x
    else
        return newroot2sib(TChoice, tree1, tree2)
    end
end


-- p^n

local function lp_star(tree1, n)
    local tree
    n = tonumber(n)
    assert(type(n) == 'number')
    if n >= 0 then -- seq tree1 (seq tree1 ... (seq tree1 (rep tree1)))
        tree = newtree((n + 1) * (tree1.size + 1))
        if lpcode.checkaux(tree1, PEnullable, 1) then
            error("loop body may accept empty string")
        end
        local start = 1
        for i = 1, n do -- repeat 'n' times
            seqaux(tree, tree1, start, tree1.size)
            start = start + tree[start].ps
        end
        tree[start].tag = TRep;
        for i = 1, tree1.size do
            copy(tree[start + i], tree1[i])
        end
    else -- choice (seq tree1 ... choice tree1 true ...) true
        n = -n;
        -- size = (choice + seq + tree1 + true) * n, but the last has no seq
        tree = newtree(n * (tree1.size + 3) - 1)
        local start = 1
        for i = n, 2, -1 do -- repeat (n - 1) times
            tree[start].tag = TChoice;
            tree[start].ps = i * (tree1.size + 3) - 2
            tree[start + tree[start].ps].tag = TTrue;
            start = start + 1
            seqaux(tree, tree1, start, tree1.size)
            start = start + tree[start].ps
        end
        tree[start].tag = TChoice;
        tree[start].ps = tree1.size + 1
        tree[start + tree[start].ps].tag = TTrue
        for i = 1, tree1.size do
            copy(tree[start + i], tree1[i])
        end
    end
    return tree
end


-- #p == &p

local function lp_and(pat)
    return newroot1sib(TAnd, pat)
end


-- -p == !p

local function lp_not(pat)
    return newroot1sib(TNot, pat)
end


-- [t1 - t2] == Seq (Not t2) t1
-- If t1 and t2 are charsets, make their difference.

local function lp_sub(pat1, pat2)
    local tree

    local tree1 = getpatt(pat1)
    local tree2 = getpatt(pat2)
    local charset1 = lpcode.tocharset(tree1, 1)
    local charset2 = lpcode.tocharset(tree2, 1)
    if charset1 and charset2 then
        tree = newcharset()
        for i = 0, 7 do
            tree[1].val[i] = band(charset1[i], bnot(charset2[i]))
        end
    else
        tree = newtree(2 + tree1.size + tree2.size)
        tree[1].tag = TSeq; -- sequence of...
        tree[1].ps = 2 + tree2.size
        tree[2].tag = TNot; -- ...not...
        for i = 1, tree2.size do -- ...t2
            copy(tree[2 + i], tree2[i])
        end
        for i = 1, tree1.size do -- ... and t1
            copy(tree[tree2.size + 2 + i], tree1[i])
        end
    end
    return tree
end


local function lp_set(pat)
    assert(type(pat) == 'string')
    local tree = newcharset()
    for i = 1, #pat do
        local b = pat:sub(i, i):byte()
        tree[1].val[rshift(b, 5)] = bor(tree[1].val[rshift(b, 5)], lshift(1, band(b, 31)))
    end
    return tree
end


local function lp_range(...)
    local args = { ... }
    local top = #args
    local tree = newcharset()
    for i = 1, top do
        assert(#args[i] == 2, args[i] .. " range must have two characters")
        for b = args[i]:sub(1, 1):byte(), args[i]:sub(2, 2):byte() do
            tree[1].val[rshift(b, 5)] = bor(tree[1].val[rshift(b, 5)], lshift(1, band(b, 31)))
        end
    end
    return tree
end


-- Look-behind predicate

local function lp_behind(pat)
    local tree1 = getpatt(pat)
    local n = lpcode.fixedlenx(tree1, 0, 0, 1)
    assert(not lpcode.hascaptures(tree1, 1), "pattern have captures")
    assert(n > 0, "pattern may not have fixed length")
    assert(n <= MAXBEHIND, "pattern too long to look behind")
    local tree = newroot1sib(TBehind, pat)
    tree[1].val = n;
    return tree
end


-- Create a non-terminal

local function lp_V(pat)
    local tree = newleaf(TOpenCall)
    assert(pat, "non-nil value expected")
    tree[1].val = pat
    return tree
end


-- Create a tree for a non-empty capture, with a body and
-- optionally with an associated Lua value (at index 'labelidx' in the
-- stack)

local function capture_aux(cap, pat, val)
    local tree = newroot1sib(TCapture, pat)
    tree[1].cap = cap
    tree[1].val = val
    return tree
end


-- Fill a tree with an empty capture, using an empty (TTrue) sibling.

local function auxemptycap(tree, cap, par, start)
    tree[start].tag = TCapture;
    tree[start].cap = cap
    tree[start].val = par
    tree[start + 1].tag = TTrue;
end


-- Create a tree for an empty capture

local function newemptycap(cap, par)
    local tree = newtree(2)
    auxemptycap(tree, cap, par, 1)
    return tree
end


-- Captures with syntax p / v
-- (function capture, query capture, string capture, or number capture)

local function lp_divcapture(pat, par)
    local typ = type(par)
    if typ == "function" then
        return capture_aux(Cfunction, pat, par)
    elseif typ == "table" then
        return capture_aux(Cquery, pat, par)
    elseif typ == "string" then
        return capture_aux(Cstring, pat, par)
    elseif typ == "number" then
        local tree = newroot1sib(TCapture, pat)
        assert(0 <= par and par <= 0xffff, "invalid number")
        tree[1].cap = Cnum;
        tree[1].val = par;
        return tree
    else
        error("invalid replacement value")
    end
end


local function lp_substcapture(pat)
    return capture_aux(Csubst, pat, 0)
end


local function lp_tablecapture(pat)
    return capture_aux(Ctable, pat, 0)
end


local function lp_groupcapture(pat, val)
    if not val then
        return capture_aux(Cgroup, pat, 0)
    else
        return capture_aux(Cgroup, pat, val)
    end
end


local function lp_foldcapture(pat, fce)
    assert(type(fce) == 'function')
    return capture_aux(Cfold, pat, fce)
end


local function lp_simplecapture(pat)
    return capture_aux(Csimple, pat, 0)
end


local function lp_poscapture()
    return newemptycap(Cposition, 0)
end


local function lp_argcapture(val)
    assert(type(val) == 'number')
    local tree = newemptycap(Carg, 0)
    tree[1].val = val;
    assert(0 < val and val <= 0xffff, "invalid argument index")
    return tree
end


local function lp_backref(val)
    assert(type(val) == 'string')
    return newemptycap(Cbackref, val)
end


-- Constant capture

local function lp_constcapture(...)
    local tree
    local args = { ... }
    local n = select('#', ...) -- number of values
    if n == 0 then -- no values?
        tree = newleaf(TTrue) -- no capture
    elseif n == 1 then
        tree = newemptycap(Cconst, args[1]) -- single constant capture
    else -- create a group capture with all values
        local start = 1
        tree = newtree(1 + 3 * (n - 1) + 2)
        tree[1].tag = TCapture
        tree[1].cap = Cgroup
        tree[1].val = 0
        start = start + 1
        for i = 1, n - 1 do
            tree[start].tag = TSeq
            tree[start].ps = 3
            auxemptycap(tree, Cconst, args[i], start + 1)
            start = start + tree[start].ps
        end
        auxemptycap(tree, Cconst, args[n], start)
    end
    return tree
end


local function lp_matchtime(pat, fce)
    assert(type(fce) == 'function')
    local tree = newroot1sib(TRunTime, pat)
    tree[1].val = fce
    return tree
end

-- ======================================================



-- ======================================================
-- Grammar - Tree generation
-- =======================================================


-- push on the stack the index and the pattern for the
-- initial rule of grammar at index 'arg' in the stack;
-- also add that index into position table.

local function getfirstrule(pat, postab)
    local key
    if type(pat[1]) == 'string' then -- access first element
        key = pat[1]
    else
        key = 1
    end
    local rule = pat[key]
    if not rule then
        error("grammar has no initial rule")
    end
    if not gettree(rule) then -- initial rule not a pattern?
        error(("initial rule '%s' is not a pattern"):format(tostring(firstrule)))
    end
    postab[key] = 1
    return key, rule
end


-- traverse grammar at index 'arg', pushing all its keys and patterns
-- into the stack. Create a new table (before all pairs key-pattern) to
-- collect all keys and their associated positions in the final tree
-- (the "position table").
-- Return the number of rules and (in 'totalsize') the total size
-- for the new tree.

local function collectrules(pat)
    local n = 1; -- to count number of rules
    local postab = {}
    local firstkeyrule, firstrule = getfirstrule(pat, postab)
    local rules = { firstkeyrule, firstrule }
    local size = 2 + firstrule.size -- TGrammar + TRule + rule
    for key, val in pairs(pat) do
        if key ~= 1 and val ~= firstrule then -- initial rule?
            if not gettree(val) then -- value is not a pattern?
                error(("rule '%s' is not a pattern"):format(tostring(key)))
            end
            rules[#rules + 1] = key
            rules[#rules + 1] = val
            postab[key] = size
            size = 1 + size + val.size
            n = n + 1
        end
    end
    size = size + 1; -- TTrue to finish list of rules
    return n, size, rules, postab
end


local function buildgrammar(grammar, rules, n, index)

    for i = 1, n do -- add each rule into new tree
        local size = rules[i * 2].size
        grammar[index].tag = TRule;
        --      grammar[index].val = 0;
        grammar[index].cap = i; -- rule number
        grammar[index].ps = size + 1; -- point to next rule
        for j = 1, size do
            copy(grammar[j + index], rules[i * 2][j]) -- copy rule
        end
        index = index + grammar[index].ps; -- move to next rule
    end
    grammar[index].tag = TTrue; -- finish list of rules
end


-- Check whether a tree has potential infinite loops

local function checkloops(tree, index)
    local tag = tree[index].tag
    if tag == TRep and lpcode.checkaux(tree, PEnullable, index + 1) then
        return true
    elseif tag == TGrammar then
        return -- sub-grammars already checked
    else
        local tag = numsiblings[tree[index].tag + 1]
        if tag == 0 then
            return
        elseif tag == 1 then
            return checkloops(tree, index + 1)
        elseif tag == 2 then
            if checkloops(tree, index + 1) then
                return true
            else
                return checkloops(tree, index + tree[index].ps)
            end
        else
            assert(false)
        end
    end
end


local function verifyerror(passed, npassed)
    local i, j;
    for i = npassed - 1, 0, -1 do -- search for a repetition
        for j = i - 1, 0, -1 do
            if passed[i] == passed[j] then
                error(("rule '%s' may be left recursive"):format(passed[i]))
            end
        end
    end
    error("too many left calls in grammar")
end


-- Check whether a rule can be left recursive; raise an error in that
-- case; otherwise return 1 iff pattern is nullable. Assume ktable at
-- the top of the stack.

local function verifyrule(tree, passed, npassed, nullable, index)
    local tag = tree[index].tag
    if tag == TChar or tag == TSet or tag == TAny or tag == TFalse then
        return nullable; -- cannot pass from here
    elseif tag == TTrue or tag == TBehind then
        return true;
    elseif tag == TNot or tag == TAnd or tag == TRep then
        return verifyrule(tree, passed, npassed, true, index + 1)
    elseif tag == TCapture or tag == TRunTime then
        return verifyrule(tree, passed, npassed, nullable, index + 1)
    elseif tag == TCall then
        return verifyrule(tree, passed, npassed, nullable, index + tree[index].ps)
    elseif tag == TSeq then -- only check 2nd child if first is nullable
        if not verifyrule(tree, passed, npassed, false, index + 1) then
            return nullable
        else
            return verifyrule(tree, passed, npassed, nullable, index + tree[index].ps)
        end
    elseif tag == TChoice then -- must check both children
        nullable = verifyrule(tree, passed, npassed, nullable, index + 1)
        return verifyrule(tree, passed, npassed, nullable, index + tree[index].ps)
    elseif tag == TRule then
        if npassed >= MAXRULES then
            return verifyerror(passed, npassed)
        else
            passed[npassed] = tree[index].val
            npassed = npassed + 1
            return verifyrule(tree, passed, npassed, nullable, index + 1)
        end
    elseif tag == TGrammar then
        return lpcode.checkaux(tree, PEnullable, index) -- sub-grammar cannot be left recursive
    else
        assert(false)
    end
end


local function verifygrammar(rule, index)
    local passed = {}
    -- check left-recursive rules
    local ind = index + 1
    while rule[ind].tag == TRule do
        if rule[ind].val then -- used rule
            verifyrule(rule, passed, 0, false, ind + 1)
        end
        ind = ind + rule[ind].ps
    end
    assert(rule[ind].tag == TTrue)
    -- check infinite loops inside rules
    ind = index + 1
    while rule[ind].tag == TRule do
        if rule[ind].val then -- used rule
            if checkloops(rule, ind + 1) then
                error(("empty loop in rule '%s'"):format(tostring(rule[ind].val)))
            end
        end
        ind = ind + rule[ind].ps
    end
    assert(rule[ind].tag == TTrue)
end


-- Give a name for the initial rule if it is not referenced

local function initialrulename(grammar, val)
    if not grammar[2].val then -- initial rule is not referenced?
        grammar[2].val = val
    end
end


function newgrammar(pat)
    -- traverse grammar at index 'arg', pushing all its keys and patterns
    -- into the stack. Create a new table (before all pairs key-pattern) to
    -- collect all keys and their associated positions in the final tree
    -- (the "position table").
    -- Return the number of rules and (in 'totalsize') the total size
    -- for the new tree.

    local n, size, rules, postab = collectrules(pat)
    local grammar = newtree(size)
    local start = 1
    grammar[start].tag = TGrammar;
    grammar[start].val = n;
    buildgrammar(grammar, rules, n, start + 1)
    finalfix(true, postab, grammar, start + 1)
    initialrulename(grammar, rules[1])
    verifygrammar(grammar, 1)
    return grammar
end

-- ======================================================


local function prepcompile(p, index)
    finalfix(false, nil, p, index)
    lpcode.compile(p, index)
    return p.code
end


local function lp_printtree(tree, c)
    if c then
        finalfix(false, nil, tree, 1)
    end
    lpprint.printtree(tree, 0, 1)
end


local function lp_printcode(pat)
    if not pat.code then -- not compiled yet?
        prepcompile(pat, 1)
    end
    lpprint.printpatt(pat.code)
end


-- Get the initial position for the match, interpreting negative
-- values from the end of the subject

local function initposition(len, pos)
    local ii = pos or 1
    if (ii > 0) then -- positive index?
        if ii <= len then -- inside the string?
            return ii - 1; -- return it (corrected to 0-base)
        else
            return len; -- crop at the end
        end
    else -- negative index
        if -ii <= len then -- inside the string?
            return len + ii -- return position from the end
        else
            return 0; -- crop at the beginning
        end
    end
end


-- Main match function

local function lp_match(pat, s, init, ...)
    local capture = {}
    local p = getpatt(pat)
    local code = p.code or prepcompile(p, 1)
    local i = initposition(s:len(), init) + 1
    local r = lpvm.match(s, i, code, capture, ...)
    if not r then
        return r
    end
    return lpcap.getcaptures(capture, s, r, ...)
end


-- {======================================================
-- Library creation and functions not related to matching
-- =======================================================

local function lp_setmax(val)
    lpvm.setmax(val)
end


local function lp_version()
    return VERSION
end


local function lp_type(pat)
    if gettree(pat) then
        return "pattern"
    end
end


local function createcat(tab, catname, catfce)
    local t = newcharset()
    for i = 0, 255 do
        if catfce(i) ~= 0 then
            t[1].val[rshift(i, 5)] = bor(t[1].val[rshift(i, 5)], lshift(1, band(i, 31)))
        end
    end
    tab[catname] = t
end


local function lp_locale(tab)
    tab = tab or {}
    createcat(tab, "alnum", function(c) return ffi.C.isalnum(c) end)
    createcat(tab, "alpha", function(c) return ffi.C.isalpha(c) end)
    createcat(tab, "cntrl", function(c) return ffi.C.iscntrl(c) end)
    createcat(tab, "digit", function(c) return ffi.C.isdigit(c) end)
    createcat(tab, "graph", function(c) return ffi.C.isgraph(c) end)
    createcat(tab, "lower", function(c) return ffi.C.islower(c) end)
    createcat(tab, "print", function(c) return ffi.C.isprint(c) end)
    createcat(tab, "punct", function(c) return ffi.C.ispunct(c) end)
    createcat(tab, "space", function(c) return ffi.C.isspace(c) end)
    createcat(tab, "upper", function(c) return ffi.C.isupper(c) end)
    createcat(tab, "xdigit", function(c) return ffi.C.isxdigit(c) end)
    return tab
end


local pattreg = {
    ["ptree"] = lp_printtree,
    ["pcode"] = lp_printcode,
    ["match"] = lp_match,
    ["B"] = lp_behind,
    ["V"] = lp_V,
    ["C"] = lp_simplecapture,
    ["Cc"] = lp_constcapture,
    ["Cmt"] = lp_matchtime,
    ["Cb"] = lp_backref,
    ["Carg"] = lp_argcapture,
    ["Cp"] = lp_poscapture,
    ["Cs"] = lp_substcapture,
    ["Ct"] = lp_tablecapture,
    ["Cf"] = lp_foldcapture,
    ["Cg"] = lp_groupcapture,
    ["P"] = lp_P,
    ["S"] = lp_set,
    ["R"] = lp_range,
    ["L"] = lp_and,
    ["locale"] = lp_locale,
    ["version"] = lp_version,
    ["setmaxstack"] = lp_setmax,
    ["type"] = lp_type,
}

metareg = {
    ["__mul"] = lp_seq,
    ["__add"] = lp_choice,
    ["__pow"] = lp_star,
    ["__len"] = lp_and,
    ["__div"] = lp_divcapture,
    ["__unm"] = lp_not,
    ["__sub"] = lp_sub,
    ["__index"] = pattreg
}


-- =======================================================
-- Enable `#pattern` in more cases
-- =======================================================

-- The following code allows to use the #pattern syntax
-- even when LuaJIT has not been compiled with
-- `-DLUAJIT_ENABLE_LUA52COMPAT`. It relies on `newproxy()`
-- and `debug.setmetatable()`. When either is absent or
-- non-functional, `#pattern` is disabled, and `L(pattern)`
-- must be used instead.

local LUA52LEN = not #setmetatable({},{__len = function()end})

local PROXIES = pcall(function()
    local prox = newproxy(true)
    local prox2 = newproxy(prox)
    assert (type(getmetatable(prox)) == "table" 
            and (getmetatable(prox)) == (getmetatable(prox2)))
end)

if PROXIES and not LUA52LEN then
    local proxycache = setmetatable({}, {__mode = "k"})
    local __index_pattreg = {__index = pattreg}
    local metareg_ = metareg
    local baseproxy = newproxy (true)
    metareg = getmetatable(baseproxy)

    for k, v in pairs(metareg_) do
        metareg[k] = v
    end

    function metareg:__index(k)
        return proxycache[self][k]
    end

    function metareg:__newindex(k, v)
        proxycache[self][k] = v
    end

    function maketree(cons)
        local pt = newproxy(baseproxy)
        setmetatable(cons, __index_pattreg)
        proxycache[pt]=cons
        return pt
    end

    -- Gives access to the table hidden behind the proxy.
    function get_concrete_tree(p) return proxycache[p] end
else
    -- LUA52LEN or restricted sandbox:
    -- if not LUA52LEN then
    --     print("Warning: The `__len` metatethod won't work with patterns, "
    --         .."use `L(pattern)` insetad of `#pattern`for lookaheads.")
    -- end
    function maketree(pt)
        return setmetatable(pt, metareg)
    end
    -- present for compatibility with the proxy mode.
    function get_concrete_tree (p) return p end
end

return pattreg