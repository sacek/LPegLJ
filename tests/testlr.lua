local lpeg = require"lpeglj"

local m = lpeg

local function checkeq(x, y, p)
    if p then print(x, y) end
    if type(x) ~= "table" then assert(x == y)
    else
        for k, v in pairs(x) do checkeq(v, y[k], p) end
        for k, v in pairs(y) do checkeq(v, x[k], p) end
    end
end

m.enableleftrecursion(true)

--[[
direct left recursion
E ← E + n / n
--]]

local pat = m.P{
    "E";
    E = m.V"E" * '+' * "n" + "n",
}

assert(pat:match("n+n+n") == 6)

--[[
indirect left recursion
L ← P.x / x
P ← P(n) / L
--]]

local pat = m.P{
    "L";
    L = m.V"P" * ".x" + "x",
    P = m.V"P" * "(n)" + m.V"L"
}

assert(pat:match("x(n)(n).x(n).x") == 15)

--[[
left and right recursion with precedence rules
E ← E1 + E2 / E1 − E2 / E2 ∗ E3 / E2 ÷ E3 / E3 ∗∗ E3 / − E4 / (E1) / n
--]]


local pat = m.P{
    "E",
    E = m.V("E", 1) * m.S'+-' * m.V("E", 2) +
            m.V("E", 2) * m.S'*/' * m.V("E", 3) +
            m.V("E", 3) * '**' * m.V("E", 3) +
            '-' * m.V("E", 4) +
            '(' * m.V("E") * ')' +
            m.R'09' ^ 1,
}

assert(pat:match("-1*(6+2/4+3-1)**2") == 18)

--[[
left and right recursion with precedence rules
E ← E1 + E2 / E1 − E2 / E2 ∗ E3 / E2 ÷ E3 / E3 ∗∗ E3 / − E4 / (E1) / n
create AST tree
--]]


local pat = m.P{
    "E",
    E = m.Ct(m.V("E", 1) * m.C(m.S'+-') * m.V("E", 2) +
            m.V("E", 2) * m.C(m.S'*/') * m.V("E", 3) +
            m.V("E", 3) * m.C('**') * m.V("E", 3) +
            m.C('-') * m.V("E", 4) +
            '(' * m.V("E") * ')' +
            m.C(m.R'09' ^ 1)),
}

local ASTtree = pat:match("1+1+1")
checkeq(ASTtree, { { { "1" }, "+", { "1" } }, "+", { "1" } })

local ASTtree = pat:match("-1*(6+2/4+3-1)**2")
checkeq(ASTtree, { { "-", { "1" } }, "*", { { { { { { "6" }, "+", { { "2" }, "/", { "4" } } }, "+", { "3" } }, "-", { "1" } } }, "**", { "2" } } })

--[[
simple evaluator
E ← E1 + E2 / E1 − E2 / E2 ∗ E3 / E2 ÷ E3 / E3 ∗∗ E3 / − E4 / (E1) / n
--]]

local eval = function(s, i, p1, p2, p3)
    local res
    if p2 == '+' then
        res = p1 + p3
    elseif p2 == '-' then
        res = p1 - p3
    elseif p2 == '*' then
        res = p1 * p3
    elseif p2 == '/' then
        res = p1 / p3
    elseif p1 == '-' then
        res = -p2
    elseif p2 == '**' then
        res = p1 ^ p3
    else
        res = p1
    end
    return true, res
end


local pat = m.P{
    "E",
    E = m.Cmt(m.V("E", 1) * m.C(m.S'+-') * m.V("E", 2) +
            m.V("E", 2) * m.C(m.S'*/') * m.V("E", 3) +
            m.V("E", 3) * m.C('**') * m.V("E", 3) +
            m.C('-') * m.V("E", 4) +
            '(' * m.V("E") * ')' +
            m.C(m.R'09' ^ 1), eval),
}

assert(pat:match("-1*(6+2/4+3-1)**2") == -72.25)
