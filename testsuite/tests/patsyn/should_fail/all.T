test('mono', normal, compile_fail, [''])
test('unidir', normal, compile_fail, [''])
test('local', normal, compile_fail, [''])
test('as-pattern', normal, compile_fail, [''])
test('T9161-1', normal, compile_fail, [''])
test('T9161-2', normal, compile_fail, [''])
test('T9705-1', normal, compile_fail, [''])
test('T9705-2', normal, compile_fail, [''])
test('unboxed-bind', normal, compile_fail, [''])
test('unboxed-wrapper-naked', normal, compile_fail, [''])
test('T10873', normal, compile_fail, [''])
test('T11010', normal, compile_fail, [''])
test('records-check-sels', normal, compile_fail, [''])
test('records-no-uni-update', normal, compile_fail, [''])
test('records-no-uni-update2', normal, compile_fail, [''])
test('records-mixing-fields', normal, compile_fail, [''])
test('records-exquant', normal, compile_fail, [''])
test('records-poly-update', normal, compile_fail, [''])
test('mixed-pat-syn-record-sels', normal, compile_fail, [''])
test('T11039', normal, compile_fail, [''])
test('T11039a', normal, compile, [''])
test('export-type', normal, compile_fail, [''])
test('export-syntax', normal, compile_fail, [''])
test('import-syntax', normal, compile_fail, [''])
test('export-class', normal, compile_fail, [''])
test('poly-export-fail2', expect_broken(10653), compile_fail, [''])
test('export-super-class-fail', expect_broken(10653), compile_fail, [''])
test('export-type-synonym', normal, compile_fail, [''])
test('export-ps-rec-sel', normal, compile_fail, [''])
test('T11053', normal, compile, ['-fwarn-missing-pattern-synonym-signatures'])
test('T10426', normal, compile_fail, [''])
test('T11265', normal, compile_fail, [''])
test('T11667', normal, compile_fail, [''])
test('T12165', normal, compile_fail, [''])
test('T12819', normal, compile_fail, [''])
