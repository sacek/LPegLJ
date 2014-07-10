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
*set* - enable left recursion
####lpeglj.V(v, p)
*p* - precedence level (number 1 to n)
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
*set* - enable memoization (true or false)

###Using stream:
####lpeglj.streammatch(pat, init, ...)
*pat* - pattern   
*init* - start position in stream (should be positive number)  
*...* - another parameters (same as in lpeg.match function)  

Returns function **func**. This function is called with string data from stream.    
  
####func(str, eos)
*str* - string input (string)  
*eos* - end of stream (boolean)  
Returns **status** and captures or position.     

**Status**:  
 1 - need another data   
-1 - parsing fail  
 0 - parsing finished    

Restrictions and differences for stream mode:  

- start position in stream should be positive number.
- using lpeg.B(patt) is not secure now (NYI) - input buffers can be deleted.
- whole string argument in runtime captures (Cmt and function) is not string but function.
  This function takes two arguments (start and end index of string in stream) and return string. 
 
###Example:
```Lua
local lpeglj = require"lpeglj"
local pat = m.C("abc") * m.C("def")
local fce = pat:streammatch()
local st = fce("ab") -- return 1 - need another data
local st, cap = fce("c") -- return 1 , "abc"  - capture and need another data
local st, cap = fce("def") -- return 0 , "def"  - capture and finish parsing
```



