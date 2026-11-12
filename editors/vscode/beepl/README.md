# BeePL for VS Code

Highlights `.bpl` files using your current editor theme: functions, types,
effects, keywords, numbers, strings, BPF helpers, section annotations, and nested
`(* ... *)` comments. Includes bracket pairing and `bfun`, `bmatch`, `bgpl`,
`bxdp`, and `bmap` snippets. This extension contains no executable activation
code and does not run the compiler or send data anywhere.

## Install

From the repository root:

```sh
make -C editors/vscode/beepl package
code --install-extension editors/vscode/beepl/dist/beepl-language-0.1.0.vsix
```

Alternatively, open Extensions in VS Code, choose **Install from VSIX...** from
the menu, and select that file. Reload the editor if prompted and open a `.bpl`
file. The status bar should show **BeePL**; click the language name and select
BeePL if an existing file association overrides it. In Remote SSH/WSL, install
in the VS Code window where you edit the repository. No Marketplace publishing
or account is needed. Uninstall with `code --uninstall-extension beepl.beepl-language`.

This provides syntax colors and snippets, not semantic diagnostics, completion,
go-to-definition, or a language server. Use the repository Makefiles to compile.
Colors depend on your theme. Toggle a block comment with the standard VS Code
block-comment command. BeePL has no C-style `//` comments.

## Development

The grammar follows `bparser/beepl_lexer.mll`. To run real TextMate tokenization
tests, install the development dependencies with `npm install`, then `make test`.
Packaging only needs Python 3. The VSIX contains only the declared language,
grammar, configuration, snippets and this guide; development dependencies are
not included.
