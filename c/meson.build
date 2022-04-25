project('expr-parsing', 'c')

cc = meson.get_compiler('c')
m_dep = cc.find_library('m', required : false)

executable('expr', 'expr.c', dependencies: m_dep)

