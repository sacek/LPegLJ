LPegLJ v.20
===========
## New functions:
###Loading and saving patterns:
####pat:save(fname, tree)
fname - file name for pattern
tree - full pattern tree is saved
####lpeg.load(fname)
fname - file name with pattern
###Example:
```Lua
local lpeglj = require"lpeglj"
local pat = lpeglj.P('abc')
pat:save("saved.pat")  -- save only pattern code
local savedpat = lpeglj.load("saved.pat")
```
###Left recursion:
####lpeglj.enableleftrecursion(set)
set - enable left recursion
####lpeglj.V(v, p)
p - precedence level
###Example:
```Lua
local lpeglj = require"lpeglj"
lpeglj.enableleftrecursion(true)
local pat = m.P{
    "E",
    E = lpeglj.V("E", 1) * '+' * lpeglj.V("E", 2) +   -- left associative rule with low precedence
     lpeglj.V("E", 2) * '**' * lpeglj.V("E", 2) +     -- right associative rule with higher precedence
    'n'
    }
pat:match("n+n+n")
```
####using re module with precedence
```Lua
local lpeglj = require"lpeglj"
local re = require"re"
lpeglj.enableleftrecursion(true)
local pat = [[
     E <- E:1 [+-] E:2 / -- left associativity
          E:2 [*/] E:3 /
          E:3 '**' E:3 / -- right associativity
          '-' E:4 /      -- highest precedence
          '(' E ')' /
          [0-9]+
]]
re.match("-1*(6+2/4+3-1)**2", pat)
```
###Using memoization:
####lpeglj.enablememoization(set)
set - enable memoization
