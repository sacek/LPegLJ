local m = require"lpeglj"


local function checkeq(x, y, p)
    if p then print(x, y) end
    if type(x) ~= "table" then assert(x == y)
    else
        for k, v in pairs(x) do checkeq(v, y[k], p) end
        for k, v in pairs(y) do checkeq(v, x[k], p) end
    end
end

local ret

print"Tests for LPegLJ stream mode"

assert(type(m.version()) == "string")
print("version " .. m.version())

local pat = m.C('abcd') * m.C('x')
local fce = pat:streammatch()

ret = { fce("a") }
checkeq(ret, { 1 })
ret = { fce("b") }
checkeq(ret, { 1 })
ret = { fce("c") }
checkeq(ret, { 1 })
ret = { fce("d") }
checkeq(ret, { 1, "abcd" })
ret = { fce("x") }
checkeq(ret, { 0, 'x' })

local pat = m.C('abcd') * m.C('x') + m.C('abcd') * m.C('y')
local fce = pat:streammatch()
ret = { fce("abcd") }
checkeq(ret, { 1 })
ret = { fce("y") }
checkeq(ret, { 0, "abcd", "y" })

local pat = m.C('abcd') ^ 0 * m.C('x')
local fce = pat:streammatch()
for i = 1, 1e3 do
    ret = { fce("ab") }
    checkeq(ret, { 1 })
    ret = { fce("cd") }
    checkeq(ret, { 1, "abcd" })
end
ret = { fce("x") }
checkeq(ret, { 0, "x" })

local pat = (m.C('abcd') / "out") ^ 0 * m.C('x')
local fce = pat:streammatch()
for i = 1, 1e3 do
    ret = { fce("ab") }
    checkeq(ret, { 1 })
    ret = { fce("cd") }
    checkeq(ret, { 1, "out" })
end
ret = { fce("x") }
checkeq(ret, { 0, "x" })

local pat = (m.C('abcd') / "pattern1" + m.C('efgh') / "pattern2" + (m.P(1) - 'xyz')) ^ 0 * (m.C("xyz") / "pattern3")
local fce = pat:streammatch()

for i = 1, 1e3 do
    ret = { fce("ef") }
    checkeq(ret, { 1 })
    ret = { fce("gh") }
    checkeq(ret, { 1, "pattern2" })
    ret = { fce("a") }
    checkeq(ret, { 1 })
    ret = { fce("bcd") }
    checkeq(ret, { 1, "pattern1" })
end
ret = { fce("xyz") }
checkeq(ret, { 0, "pattern3" })

local pat = m.P('abcd') * -1
local fce = pat:streammatch()
ret = { fce("abc") }
checkeq(ret, { 1 })
ret = { fce("d") }
checkeq(ret, { 1 })
ret = { fce("", true) }
checkeq(ret, { 0, 5 })

print('OK')

