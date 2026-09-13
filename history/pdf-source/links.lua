local base = 'https://github.com/subfish-zhou/star-shaped-kakeya-lean/blob/6432d8eb33cc2093ed5ca1f5e63390e4bf065fd0/'
function Link(el)
  if not el.target:match('^%a[%w+.-]*:') and not el.target:match('^#') then
    el.target = base .. el.target
  end
  return el
end
function Code(el)
  local s=el.text:gsub('\\','\\textbackslash{}'):gsub('([#$%%&_{}])','\\%1')
  if el.text:find('%s') then return pandoc.RawInline('latex','\\texttt{' .. s .. '}') end
  return pandoc.RawInline('latex', '\\code{' .. s .. '}')
end
function Para(el)
  if pandoc.utils.stringify(el):match('^9 月 5 日的简短证明') then
    return {pandoc.RawBlock('latex','{\\emergencystretch=2em'),el,pandoc.RawBlock('latex','\\par}')}
  end
end
function Str(el)
  local s=el.text
  if not s:match('%d+%.%d+') then return nil end
  local result={}; local cursor=1
  while true do
    local a,b=s:find('%d+%.%d+',cursor)
    if not a then break end
    if a>cursor then table.insert(result,pandoc.Str(s:sub(cursor,a-1))) end
    table.insert(result,pandoc.RawInline('latex','\\allowbreak{}'))
    table.insert(result,pandoc.Str(s:sub(a,b)))
    cursor=b+1
  end
  if cursor<=#s then table.insert(result,pandoc.Str(s:sub(cursor))) end
  return result
end
