# isabelle.vim

Supporting plugin for [`coc-isabelle`](https://github.com/ThreeFx/coc-isabelle).
It defines the dynamic syntax highlighting groups used by coc-isabelle, as well
normal Isabelle/Isar syntax.

This plugin can technically be used standalone, however it will only provide
static syntax highlighting and symbol substitution. In order to take full
advantage of the Isabelle/VSCode language server (which is only called VSCode,
it is a generic language server), you have to use `coc-isabelle`.

## Installation

Install it using your favorite vim package manager:

```
Plug 'ThreeFx/isabelle.vim'
```

## Configuration

|Variable|Default|Description|
|--------|-------|-----------|
|`g:isabelle_output_height`|10|Height of the Isabelle output window|
|`g:isabelle_process_width`|40|Height of the Isabelle process window|

## Screenshots/Features

#### Overview

Fairly similar to the PIDE overview. The progress and output windows are simply
buffers named `-PROGRESS-` and `-OUTPUT-`, making the layout easily
configurable.

![](screenshots/overview.png)

#### Sledgehammer + Code Action

Code actions are supported for `sledgehammer`, `try` and `try0`. These are
mainly based on string parsing though, so beware.

![](screenshots/sledgehammer.png)

#### Proof skeletons

Code actions are also supported for proof skeletons.

![](screenshots/codeaction_before.png)
![](screenshots/codeaction_after.png)
