# Tests for pattern match checker (coverage and exhaustiveness)

# Just do the normal way...
def f( name, opts ):
  opts.only_ways = ['normal']

setTestOpts(f)

# Overloaded Lists
test('T9951a', only_compiler_types(['ghc']), compile, ['-fwarn-incomplete-patterns'])

# Overloaded Strings
test('T9951b', only_compiler_types(['ghc']), compile, ['-fwarn-incomplete-patterns'])

# other examples..
# test('ds002', normal, compile, [''])
# test('ds003', normal, compile, [''])

