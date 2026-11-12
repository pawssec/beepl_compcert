const fs = require('fs');
const path = require('path');
const assert = require('assert');
const tm = require('vscode-textmate');
const onig = require('vscode-oniguruma');
(async () => {
  const bytes = fs.readFileSync(require.resolve('vscode-oniguruma/release/onig.wasm'));
  await onig.loadWASM(bytes.buffer.slice(bytes.byteOffset, bytes.byteOffset + bytes.byteLength));
  const root = path.resolve(__dirname, '..');
  const registry = new tm.Registry({
    onigLib: Promise.resolve({createOnigScanner: p => new onig.OnigScanner(p), createOnigString: s => new onig.OnigString(s)}),
    loadGrammar: async () => JSON.parse(fs.readFileSync(path.join(root,'syntaxes/beepl.tmLanguage.json'),'utf8'))
  });
  const grammar = await registry.loadGrammar('source.beepl');
  const check = (line, token, scope) => {
    const start = line.indexOf(token);
    const result = grammar.tokenizeLine(line, tm.INITIAL);
    assert(result.tokens.some(t => t.startIndex <= start && t.endIndex >= start + token.length && t.scopes.includes(scope)), line + ' -> ' + token);
  };
  check('fun xdp_pass (uint32 x) : int32, io { 2 }', 'xdp_pass', 'entity.name.function.beepl');
  check('let slot : oulong* = none in 0', 'oulong', 'storage.type.beepl');
  check('let slot : option(option(int32*)) = some (none int32*) in 0', 'option', 'storage.type.beepl');
  check('#section raw_tracepoint/sys_enter', 'raw_tracepoint/sys_enter', 'entity.name.section.beepl');
  check('#section .maps', '#section', 'keyword.control.directive.beepl');
  check('bpf_map_lookup_elem(counts, key)', 'bpf_map_lookup_elem', 'support.function.beepl');
  check('let text : int8[4] = "GPL"', 'GPL', 'string.quoted.double.beepl');
  check('(* outer (* nested *) still comment *) let n = 42', 'still comment', 'comment.block.beepl');
  check('(* outer (* nested *) still comment *) let n = 42', '42', 'constant.numeric.beepl');
  let state = grammar.tokenizeLine('(* outer', tm.INITIAL).ruleStack;
  let result = grammar.tokenizeLine('(* inner *) still outer', state);
  assert(result.tokens.every(t => t.scopes.includes('comment.block.beepl')));
  result = grammar.tokenizeLine('*) let n = 1', result.ruleStack);
  assert(result.tokens.some(t => t.scopes.includes('keyword.control.beepl')));
  const repo = path.resolve(root, '../../..');
  let count = 0;
  for (const dir of ['evaluation/examples','evaluation/applications']) {
    for (const file of fs.readdirSync(path.join(repo,dir)).filter(f=>f.endsWith('.bpl'))) {
      state = tm.INITIAL;
      for(const line of fs.readFileSync(path.join(repo,dir,file),'utf8').split('\n')) state=grammar.tokenizeLine(line,state).ruleStack;
      count++;
    }
  }
  console.log(`TextMate scope checks passed; tokenized ${count} BeePL programs.`);
})().catch(error=>{console.error(error);process.exit(1)});
