"
" Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
"
" SPDX-License-Identifier: BSD-2-Clause
"

"
" Parts of this file were originally contributed by
" Jens-Wolfhard Schicke-Uffmann <drahflow@gmx.de>
"
 
"
" Vim syntax highlighting for THY files.
"
" This syntax will show UTF-8 Isabelle symbols if you have concealling enabled.
" If you use this, you will probably want it automatically enabled whenever you
" open an Isabelle theory. So whenever you detect and enable the syntax, set
" the conceal level as well:
"
"  au BufRead,BufNewFile *.thy setfiletype isabelle
"  au BufRead,BufNewFile *.thy set conceallevel=2
"
" If you regularly need to toggle this on and off you can bind it to a key:
"
"  function! ToggleConceal()
"    if &conceallevel == 0
"      set conceallevel=2
"    else
"      set conceallevel=0
"    endif
"  endfunction
"  nm <F6> :call ToggleConceal()<CR>
"  imap <F6> <C-o>:call ToggleConceal()<CR>
"

syn clear
syn sync fromstart
syn case match

syn keyword IsabelleCommand term typ prop prf full_prf pr value
syn keyword IsabelleCommand abbreviation
syn keyword IsabelleCommand theory
syn keyword IsabelleCommand theorem schematic_theorem corollary
    \ schematic_corollary
syn keyword IsabelleCommand lemma
syn keyword IsabelleCommand lemmas
syn keyword IsabelleCommand schematic_lemma
syn keyword IsabelleCommand primrec
syn keyword IsabelleCommand datatype
syn keyword IsabelleCommand declare declaration syntax_declaration
syn keyword IsabelleCommand definition
syn keyword IsabelleCommand fun
syn keyword IsabelleCommand function termination
syn keyword IsabelleCommand typedecl
syn keyword IsabelleCommand types
syn keyword IsabelleCommand typedef
syn keyword IsabelleCommand type_synonym
syn keyword IsabelleCommand consts
syn keyword IsabelleCommand constdefs
syn keyword IsabelleCommand inductive
syn keyword IsabelleCommand inductive_set
syn keyword IsabelleCommand inductive_cases
syn keyword IsabelleCommand record
syn keyword IsabelleCommand defs
syn keyword IsabelleCommand axclass
syn keyword IsabelleCommand instance
syn keyword IsabelleCommand axioms
syn keyword IsabelleCommand axiomatization
syn keyword IsabelleCommand locale
syn keyword IsabelleCommand sublocale
syn keyword IsabelleCommand theorems
syn keyword IsabelleCommand class subclass
syn keyword IsabelleCommand interpretation interpret
syn keyword IsabelleCommand instantiation
syn keyword IsabelleCommand context
syn keyword IsabelleCommand rep_datatype
syn keyword IsabelleCommand export_code
syn keyword IsabelleCommand code_const
syn keyword IsabelleCommand ML_file
syn keyword IsabelleCommand setup
syn keyword IsabelleCommand thm find_theorems
syn keyword IsabelleCommand print_theorems print_locale print_locales
    \ print_dependencies print_interps print_classes class_deps print_abbrevs
    \ print_statement print_trans_rules print_cases print_induct_rules
syn keyword IsabelleCommand notepad
syn keyword IsabelleCommand nonterminal syntax no_syntax translations
    \ no_translations

" Do some juggling to give us ML highlighting inside an Isabelle/ML block.
if exists('b:current_syntax')
  let s:current_syntax=b:current_syntax
  unlet b:current_syntax
endif
syntax include @SML syntax/sml.vim
if exists('s:current_syntax')
  let b:current_syntax=s:current_syntax
else
  unlet b:current_syntax
endif
syntax region IsabelleCommand matchgroup=SpecialComment fold start="ML\_s*\({\*\|\\<open>\)" end="\(\*}\|\\<close>\)" contains=@SML
syntax region IsabelleCommand matchgroup=SpecialComment fold start="method_setup\_s*\a\w*\_s*=\_s*\({\*\|\\<open>\)" end="\(\*}\|\\<close>\)\_s*\(\"[^\"]*\"\)\?" contains=@SML

" Excessively complicated way of matching (* ... *) comments to support nested
" blocks.
syntax region IsabelleComment matchgroup=IsabelleComment start="(\*" end="\*)" contains=IsabelleCommentStart
syntax match IsabelleCommentStart "(\*" contained nextgroup=IsabelleCommentContent contains=IsabelleCommentStart
syntax match IsabelleCommentContent ".*" contained

syntax region IsabelleComment matchgroup=IsabelleComment fold start="\\<comment>\s*\\<open>" end="\\<close>" contains=IsabelleSpecial keepend

" You can use LaTeX within text {* ... *} blocks and friends and sometimes it
" is useful to have syntax highlighting enabled within these blocks when
" working on a PDF-destined theory. This is off by default because it can be a
" little distracting when not working on documentation. You can put something
" like the following in your ~/.vimrc for easy toggling of LaTeX syntax:
"
"   function! ToggleIsabelleTex()
"     if exists('g:isabelle_tex')
"       let g:isabelle_tex = !g:isabelle_tex
"     else
"       let g:isabelle_tex=1
"     endif
"     syntax off
"     syntax on
"   endfunction
"   nm <F8> :call ToggleIsabelleTex()<CR>
"   imap <F8> <C-o>:call ToggleIsabelleTex()<CR>
"
if exists('g:isabelle_tex') && g:isabelle_tex == 1
  if exists('b:current_syntax')
    let s:current_syntax=b:current_syntax
    unlet b:current_syntax
  endif
  syntax include @TEX syntax/tex.vim
  if exists('s:current_syntax')
    let b:current_syntax=s:current_syntax
  else
    unlet b:current_syntax
  endif
  syntax region IsabelleCommand matchgroup=IsabelleComment fold start="\(chapter\|text\|txt\|header\|\(sub\)*section\)[ ]*{\*" end="\*}" contains=@TEX
  " The TeX syntax meddles with iskeyword and thereby screws up syntax
  " highlighting for anything involving an underscore after it has been loaded.
  " Reset this here.
  set iskeyword+=_
else
  " If g:isabelle_tex is not set, just highlight these blocks as normal
  " comments.
  syn match IsabelleComment "\(chapter\|text\|txt\|header\|\(sub\)*section\)[ ]*{\*\_.\{-}\*}"
endif

syn keyword IsabelleCommandPart and is
syn keyword IsabelleCommandPart assumes constrains defines shows fixes notes
    \ obtains
syn keyword IsabelleCommandPart where for
syn keyword IsabelleCommandPart begin end
syn keyword IsabelleCommandPart imports
syn keyword IsabelleCommandPart keywords uses
syn keyword IsabelleCommandPart monos overloaded
syn keyword IsabelleCommandMod code simp iff rule_format cong
syn match IsabelleCommandMod /\<intro\>!\?/
syn match IsabelleCommandMod /\<dest\>!\?/
syn keyword IsabelleCommandProofProve proof
syn keyword IsabelleCommandProofProve apply
syn keyword IsabelleCommandProofProve prefer defer
syn keyword IsabelleCommandProofBad back
syn keyword IsabelleCommandProofDone done by qed apply_end
syn keyword IsabelleCommandProofFail sorry oops
syn keyword IsabelleCommandProofIsar assume show have from then thus hence
    \ presume def
syn match IsabelleGoalProofIsar /?\<thesis\>/
syn match IsabelleGoalProofIsar /?\<case\>/
syn keyword IsabelleGoalProofIsar assms
syn keyword IsabelleCommandProofIsar with next using note
syn keyword IsabelleCommandProofIsar let
syn keyword IsabelleCommandProofIsar moreover ultimately also finally
syn keyword IsabelleCommandProofIsar fix obtain where case guess
syn keyword IsabelleCommandMethod assumption fact this
syn keyword IsabelleCommandMethod rule erule drule frule
syn keyword IsabelleCommandMethod elim
syn match IsabelleCommandMethod /\<intro\>/
syn keyword IsabelleCommandMethod intro_classes intro_locales
syn keyword IsabelleCommandMethod rule_tac erule_tac drule_tac frule_tac
syn keyword IsabelleCommandMethod insert subst hypsubst
syn keyword IsabelleCommandMethod rename_tac rotate_tac
syn keyword IsabelleCommandMethod induct_tac ind_cases induct
syn keyword IsabelleCommandMethod coinduct
syn keyword IsabelleCommandMethod induct_scheme lexicographic_order relation
syn keyword IsabelleCommandMethod case_tac cases split
syn keyword IsabelleCommandMethod subgoal_tac
syn keyword IsabelleCommandMethod eval evaluation
syn keyword IsabelleCommandMethod fail succeed
syn keyword IsabelleCommandMethod atomize atomize_elim
syn keyword IsabelleCommandMethod neg_clausify finish_clausify
syn keyword IsabelleCommandMethod contradiction
syn keyword IsabelleCommandMethod cut_tac
syn keyword IsabelleCommandMethod fold unfold unfold_locales unfolding
syn keyword IsabelleCommandMethod normalization sring_norm
syn match IsabelleCommandMethodMod /\<add!\?:/
syn match IsabelleCommandMethodMod /\<del!\?:/
syn match IsabelleCommandMethodMod /\<only!\?:/
syn match IsabelleCommandMethodMod /\<dest!\?:/
syn match IsabelleCommandMethodMod /\<intro!\?:/
syn match IsabelleCommandMethodMod /\<split!\?:/
syn match IsabelleCommandMethodMod /\<cong!\?:/
syn match IsabelleCommandMethodMod /\<arbitrary!\?:/
syn keyword IsabelleCommandMethodMod in no_asm_use
syn keyword IsabelleCommandMethodMod thin_tac
syn keyword IsabelleCommandBigMethod simp simp_all
syn keyword IsabelleCommandBigMethod blast force auto fast best slow deepen fastforce
syn keyword IsabelleCommandBigMethod unat_arith arith algebra
syn keyword IsabelleCommandBigMethod bestsimp fastsimp simplesubst slowsimp
syn keyword IsabelleCommandBigMethod clarify safe clarsimp default
syn keyword IsabelleCommandBigMethod eprover eproverF eproverH
syn keyword IsabelleCommandBigMethod iprover
syn keyword IsabelleCommandBigMethod metis metisF metisH
syn keyword IsabelleCommandBigMethod meson order pat_completeness
syn keyword IsabelleCommandBigMethod presburger
syn keyword IsabelleCommandBigMethod rtrancl rtranclp trancl tranclp
syn keyword IsabelleCommandBigMethod sat satx
syn keyword IsabelleCommandBigMethod spass spassF spassH
syn keyword IsabelleCommandBigMethod tactic raw_tactic
syn keyword IsabelleCommandBigMethod vampire vampireF vampireH
syn keyword IsabelleCommandRule conjI conjE conjunct1 conjunct2
syn keyword IsabelleCommandRule disjI1 disjI2 disjE disjCI
syn keyword IsabelleCommandRule notI notE
syn keyword IsabelleCommandRule impI
syn keyword IsabelleCommandRule mp
syn keyword IsabelleCommandRule ssubst subst
syn keyword IsabelleCommandRule contrapos_np contrapos_nn
syn keyword IsabelleCommandRule contrapos_pp contrapos_pn
syn keyword IsabelleCommandRule allI allE spec
syn keyword IsabelleCommandRule exI exE
syn keyword IsabelleCommandRule the_equality
syn keyword IsabelleCommandRule some_equality someI someI2 someI_ex
syn keyword IsabelleCommandRule order_antisym
syn keyword IsabelleCommandRule sym
syn keyword IsabelleCommandRule iffD1 iffD2
syn keyword IsabelleCommandRule arg_cong
syn keyword IsabelleCommandRule mult_le_mono1
syn keyword IsabelleCommandRule mod_Suc
syn keyword IsabelleCommandRule mod_div_equality
syn keyword IsabelleCommandRule dvd_mod_imp_dvd dvd_mod dvd_trans
syn keyword IsabelleCommandRule IntI IntD1 IntD2
syn keyword IsabelleCommandRule Compl_iff Compl_Un Compl_partition
syn keyword IsabelleCommandRule Diff_disjoint
syn keyword IsabelleCommandRule subsetI subsetD
syn keyword IsabelleCommandRule Un_subset_iff
syn keyword IsabelleCommandRule set_ext
syn keyword IsabelleCommandRule equalityI equalityE
syn keyword IsabelleCommandRule insert_is_Un
syn keyword IsabelleCommandRule mem_Collect_eq Collect_mem_eq
syn keyword IsabelleCommandRule ballI bspec bexI bexE
syn keyword IsabelleCommandRule UN_iff UN_I UN_E Union_iff
syn keyword IsabelleCommandRule INT_iff Inter_iff
syn keyword IsabelleCommandRule card_Un_Int card_Pow
syn keyword IsabelleCommandRule n_subsets
syn keyword IsabelleCommandRule ext id_def o_def o_assoc
syn keyword IsabelleCommandRule fun_upd_apply fun_upd_upd
syn keyword IsabelleCommandRule inj_on_def surj_def bij_def
syn keyword IsabelleCommandRule inv_f_f surj_f_inv_f inv_inv_eq
syn keyword IsabelleCommandRule expand_fun_eq
syn keyword IsabelleCommandRule image_def image_compose image_Un image_Int
syn keyword IsabelleCommandRule vimage_def vimage_Compl
syn keyword IsabelleCommandRule Id_def rel_comp_def R_O_Id rel_comp_mono
syn keyword IsabelleCommandRule converse_iff Image_iff Domain_iff Range_iff
syn keyword IsabelleCommandRule rtrancl_unfold rtrancl_refl
syn keyword IsabelleCommandRule r_into_rtrancl rtrancl_trans
syn keyword IsabelleCommandRule rtrancl_induct rtrancl_idemp
syn keyword IsabelleCommandRule converse_rtrancl_induct
syn keyword IsabelleCommandRule trancl_trans trancl_converse
syn keyword IsabelleCommandRule less_than_iff wf_less_than
syn keyword IsabelleCommandRule inv_image_def wf_inv_image
syn keyword IsabelleCommandRule measure_def wf_measure
syn keyword IsabelleCommandRule lex_prod_def wf_lex_prod
syn keyword IsabelleCommandRule wf_induct
syn keyword IsabelleCommandRule mono_def monoI monoD
syn keyword IsabelleCommandRule lfp_unfold lfp_induct lfp_induct_set
syn keyword IsabelleCommandRule lfp_lowerbound
syn keyword IsabelleCommandRule gfp_unfold coinduct
syn keyword IsabelleCommandRuleMod asm of OF THEN simplified where symmetric
    \ standard
syn match IsabelleCommandRule /\<[a-zA-Z][a-zA-Z0-9_']*_def\>/
syn match IsabelleCommandPart /|/

syn region IsabelleInner matchgroup=IsabelleInnerMarker start=+"+ end=+"+ contains=@IsabelleInnerStuff

syn match IsabelleSpecial /\\<lambda>\|%/
syn match IsabelleSpecial /\\<circ>\|\<o\>/
syn match IsabelleSpecial /\<O\>/
syn match IsabelleSpecial /\./

" Collapse Isabelle escape sequences.
syn match IsabelleSpecial /\\<supseteq>/ conceal cchar=⊇
syn match IsabelleSpecial /\\<KK>/ conceal cchar=𝔎
syn match IsabelleSpecial /\\<up>/ conceal cchar=↑
syn match IsabelleSpecial /\\<otimes>/ conceal cchar=⊗
syn match IsabelleSpecial /\\<aa>/ conceal cchar=𝔞
syn match IsabelleSpecial /\\<dagger>/ conceal cchar=†
syn match IsabelleSpecial /\\<frown>/ conceal cchar=⌢
syn match IsabelleSpecial /\\<guillemotleft>/ conceal cchar=«
syn match IsabelleSpecial /\\<qq>/ conceal cchar=𝔮
syn match IsabelleSpecial /\\<X>/ conceal cchar=𝒳
syn match IsabelleSpecial /\\<triangleright>/ conceal cchar=▹
syn match IsabelleSpecial /\\<guillemotright>/ conceal cchar=»
syn match IsabelleSpecial /\\<nu>/ conceal cchar=ν
syn match IsabelleSpecial /\\<sim>/ conceal cchar=∼
syn match IsabelleSpecial /\\<rightharpoondown>/ conceal cchar=⇁
syn match IsabelleSpecial /\\<p>/ conceal cchar=𝗉
syn match IsabelleSpecial /\\<Up>/ conceal cchar=⇑
syn match IsabelleSpecial /\\<triangleq>/ conceal cchar=≜
syn match IsabelleSpecial /\\<nine>/ conceal cchar=𝟵
syn match IsabelleSpecial /\\<preceq>/ conceal cchar=≼
syn match IsabelleSpecial /\\<nabla>/ conceal cchar=∇
syn match IsabelleSpecial /\\<FF>/ conceal cchar=𝔉
syn match IsabelleSpecial /\\<Im>/ conceal cchar=ℑ
syn match IsabelleSpecial /\\<VV>/ conceal cchar=𝔙
syn match IsabelleSpecial /\\<spacespace>/ conceal cchar=␣
syn match IsabelleSpecial /\\<and>/ conceal cchar=∧
syn match IsabelleSpecial /\\<mapsto>/ conceal cchar=↦
syn match IsabelleSpecial /\\<ll>/ conceal cchar=𝔩
syn match IsabelleSpecial /\\<F>/ conceal cchar=ℱ
syn match IsabelleSpecial /\\<degree>/ conceal cchar=°
syn match IsabelleSpecial /\\<beta>/ conceal cchar=β
syn match IsabelleSpecial /\\<Colon>/ conceal cchar=∷
syn match IsabelleSpecial /\\<bool>/ conceal cchar=𝔹
syn match IsabelleSpecial /\\<e>/ conceal cchar=𝖾
syn match IsabelleSpecial /\\<lozenge>/ conceal cchar=◊
syn match IsabelleSpecial /\\<u>/ conceal cchar=𝗎
syn match IsabelleSpecial /\\<sharp>/ conceal cchar=♯
syn match IsabelleSpecial /\\<Longleftrightarrow>/ conceal cchar=⟺
syn match IsabelleSpecial /\\<Otimes>/ conceal cchar=⨂
syn match IsabelleSpecial /\\<EE>/ conceal cchar=𝔈
syn match IsabelleSpecial /\\<I>/ conceal cchar=ℐ
syn match IsabelleSpecial /\\<UU>/ conceal cchar=𝔘
syn match IsabelleSpecial /\\<exclamdown>/ conceal cchar=¡
syn match IsabelleSpecial /\\<dots>/ conceal cchar=…
syn match IsabelleSpecial /\\<N>/ conceal cchar=𝒩
syn match IsabelleSpecial /\\<kk>/ conceal cchar=𝔨
syn match IsabelleSpecial /\\<plusminus>/ conceal cchar=±
syn match IsabelleSpecial /\\<E>/ conceal cchar=ℰ
syn match IsabelleSpecial /\\<triangle>/ conceal cchar=△
syn match IsabelleSpecial /\\<eta>/ conceal cchar=η
syn match IsabelleSpecial /\\<triangleleft>/ conceal cchar=◃
syn match IsabelleSpecial /\\<chi>/ conceal cchar=χ
syn match IsabelleSpecial /\\<z>/ conceal cchar=𝗓
syn match IsabelleSpecial /\\<hungarumlaut>/ conceal cchar=˝
syn match IsabelleSpecial /\\<partial>/ conceal cchar=∂
syn match IsabelleSpecial /\\<three>/ conceal cchar=𝟯
syn match IsabelleSpecial /\\<lesssim>/ conceal cchar=≲
syn match IsabelleSpecial /\\<subset>/ conceal cchar=⊂
syn match IsabelleSpecial /\\<H>/ conceal cchar=ℋ
syn match IsabelleSpecial /\\<leftarrow>/ conceal cchar=←
syn match IsabelleSpecial /\\<PP>/ conceal cchar=𝔓
syn match IsabelleSpecial /\\<sqsupseteq>/ conceal cchar=⊒
syn match IsabelleSpecial /\\<R>/ conceal cchar=ℛ
syn match IsabelleSpecial /\\<bowtie>/ conceal cchar=⨝
syn match IsabelleSpecial /\\<C>/ conceal cchar=𝒞
syn match IsabelleSpecial /\\<ddagger>/ conceal cchar=‡
syn match IsabelleSpecial /\\<ff>/ conceal cchar=𝔣
syn match IsabelleSpecial /\\<turnstile>/ conceal cchar=⊢
syn match IsabelleSpecial /\\<bar>/ conceal cchar=¦
syn match IsabelleSpecial /\\<propto>/ conceal cchar=∝
syn match IsabelleSpecial /\\<S>/ conceal cchar=𝒮
syn match IsabelleSpecial /\\<vv>/ conceal cchar=𝔳
syn match IsabelleSpecial /\\<lhd>/ conceal cchar=⊲
syn match IsabelleSpecial /\\<paragraph>/ conceal cchar=¶
syn match IsabelleSpecial /\\<mu>/ conceal cchar=μ
syn match IsabelleSpecial /\\<rightharpoonup>/ conceal cchar=⇀
syn match IsabelleSpecial /\\<Inter>/ conceal cchar=⋂
syn match IsabelleSpecial /\\<o>/ conceal cchar=𝗈
syn match IsabelleSpecial /\\<asymp>/ conceal cchar=≍
syn match IsabelleSpecial /\\<Leftarrow>/ conceal cchar=⇐
syn match IsabelleSpecial /\\<Sqinter>/ conceal cchar=⨅
syn match IsabelleSpecial /\\<eight>/ conceal cchar=𝟴
syn match IsabelleSpecial /\\<succeq>/ conceal cchar=≽
syn match IsabelleSpecial /\\<forall>/ conceal cchar=∀
syn match IsabelleSpecial /\\<complex>/ conceal cchar=ℂ
syn match IsabelleSpecial /\\<GG>/ conceal cchar=𝔊
syn match IsabelleSpecial /\\<Coprod>/ conceal cchar=∐
syn match IsabelleSpecial /\\<L>/ conceal cchar=ℒ
syn match IsabelleSpecial /\\<WW>/ conceal cchar=𝔚
syn match IsabelleSpecial /\\<leadsto>/ conceal cchar=↝
syn match IsabelleSpecial /\\<D>/ conceal cchar=𝒟
syn match IsabelleSpecial /\\<angle>/ conceal cchar=∠
syn match IsabelleSpecial /\\<section>/ conceal cchar=§
syn match IsabelleSpecial /\\<TTurnstile>/ conceal cchar=⊫
syn match IsabelleSpecial /\\<mm>/ conceal cchar=𝔪
syn match IsabelleSpecial /\\<T>/ conceal cchar=𝒯
syn match IsabelleSpecial /\\<alpha>/ conceal cchar=α
syn match IsabelleSpecial /\\<leftharpoondown>/ conceal cchar=↽
syn match IsabelleSpecial /\\<rho>/ conceal cchar=ρ
syn match IsabelleSpecial /\\<wrong>/ conceal cchar=≀
syn match IsabelleSpecial /\\<l>/ conceal cchar=𝗅
syn match IsabelleSpecial /\\<doteq>/ conceal cchar=≐
syn match IsabelleSpecial /\\<times>/ conceal cchar=×
syn match IsabelleSpecial /\\<noteq>/ conceal cchar=≠
syn match IsabelleSpecial /\\<rangle>/ conceal cchar=⟩
syn match IsabelleSpecial /\\<div>/ conceal cchar=÷
syn match IsabelleSpecial /\\<Longrightarrow>/ conceal cchar=⟹
syn match IsabelleSpecial /\\<BB>/ conceal cchar=𝔅
syn match IsabelleSpecial /\\<sqsupset>/ conceal cchar=⊐
syn match IsabelleSpecial /\\<rightarrow>/ conceal cchar=→
syn match IsabelleSpecial /\\<real>/ conceal cchar=ℝ
syn match IsabelleSpecial /\\<hh>/ conceal cchar=𝔥
syn match IsabelleSpecial /\\<Phi>/ conceal cchar=Φ
syn match IsabelleSpecial /\\<integral>/ conceal cchar=∫
syn match IsabelleSpecial /\\<CC>/ conceal cchar=ℭ
syn match IsabelleSpecial /\\<euro>/ conceal cchar=€
syn match IsabelleSpecial /\\<xx>/ conceal cchar=𝔵
syn match IsabelleSpecial /\\<Y>/ conceal cchar=𝒴
syn match IsabelleSpecial /\\<zeta>/ conceal cchar=ζ
syn match IsabelleSpecial /\\<longleftarrow>/ conceal cchar=⟵
syn match IsabelleSpecial /\\<a>/ conceal cchar=𝖺
syn match IsabelleSpecial /\\<onequarter>/ conceal cchar=¼
syn match IsabelleSpecial /\\<And>/ conceal cchar=⋀
syn match IsabelleSpecial /\\<downharpoonright>/ conceal cchar=⇂
syn match IsabelleSpecial /\\<phi>/ conceal cchar=φ
syn match IsabelleSpecial /\\<q>/ conceal cchar=𝗊
syn match IsabelleSpecial /\\<Rightarrow>/ conceal cchar=⇒
syn match IsabelleSpecial /\\<clubsuit>/ conceal cchar=♣
syn match IsabelleSpecial /\\<ggreater>/ conceal cchar=≫
syn match IsabelleSpecial /\\<two>/ conceal cchar=𝟮
syn match IsabelleSpecial /\\<succ>/ conceal cchar=≻
syn match IsabelleSpecial /\\<AA>/ conceal cchar=𝔄
syn match IsabelleSpecial /\\<lparr>/ conceal cchar=⦇
syn match IsabelleSpecial /\\<Squnion>/ conceal cchar=⨆
syn match IsabelleSpecial /\\<HH>/ conceal cchar=ℌ
syn match IsabelleSpecial /\\<sqsubseteq>/ conceal cchar=⊑
syn match IsabelleSpecial /\\<QQ>/ conceal cchar=𝔔
syn match IsabelleSpecial /\\<setminus>/ conceal cchar=∖
syn match IsabelleSpecial /\\<Lambda>/ conceal cchar=Λ
syn match IsabelleSpecial /\\<Re>/ conceal cchar=ℜ
syn match IsabelleSpecial /\\<J>/ conceal cchar=𝒥
syn match IsabelleSpecial /\\<gg>/ conceal cchar=𝔤
syn match IsabelleSpecial /\\<hyphen>/ conceal cchar=­
syn match IsabelleSpecial /\\<B>/ conceal cchar=ℬ
syn match IsabelleSpecial /\\<Z>/ conceal cchar=𝒵
syn match IsabelleSpecial /\\<ww>/ conceal cchar=𝔴
syn match IsabelleSpecial /\\<lambda>/ conceal cchar=λ
syn match IsabelleSpecial /\\<onehalf>/ conceal cchar=½
syn match IsabelleSpecial /\\<f>/ conceal cchar=𝖿
syn match IsabelleSpecial /\\<Or>/ conceal cchar=⋁
syn match IsabelleSpecial /\\<v>/ conceal cchar=𝗏
syn match IsabelleSpecial /\\<natural>/ conceal cchar=♮
syn match IsabelleSpecial /\\<seven>/ conceal cchar=𝟳
syn match IsabelleSpecial /\\<Oplus>/ conceal cchar=⨁
syn match IsabelleSpecial /\\<subseteq>/ conceal cchar=⊆
syn match IsabelleSpecial /\\<rfloor>/ conceal cchar=⌋
syn match IsabelleSpecial /\\<LL>/ conceal cchar=𝔏
syn match IsabelleSpecial /\\<Sum>/ conceal cchar=∑
syn match IsabelleSpecial /\\<ominus>/ conceal cchar=⊖
syn match IsabelleSpecial /\\<bb>/ conceal cchar=𝔟
syn match IsabelleSpecial /\\<Pi>/ conceal cchar=Π
syn match IsabelleSpecial /\\<cent>/ conceal cchar=¢
syn match IsabelleSpecial /\\<diamond>/ conceal cchar=◇
syn match IsabelleSpecial /\\<mho>/ conceal cchar=℧
syn match IsabelleSpecial /\\<O>/ conceal cchar=𝒪
syn match IsabelleSpecial /\\<rr>/ conceal cchar=𝔯
syn match IsabelleSpecial /\\<twosuperior>/ conceal cchar=²
syn match IsabelleSpecial /\\<leftharpoonup>/ conceal cchar=↼
syn match IsabelleSpecial /\\<pi>/ conceal cchar=π
syn match IsabelleSpecial /\\<k>/ conceal cchar=𝗄
syn match IsabelleSpecial /\\<star>/ conceal cchar=⋆
syn match IsabelleSpecial /\\<rightleftharpoons>/ conceal cchar=⇌
syn match IsabelleSpecial /\\<equiv>/ conceal cchar=≡
syn match IsabelleSpecial /\\<langle>/ conceal cchar=⟨
syn match IsabelleSpecial /\\<Longleftarrow>/ conceal cchar=⟸
syn match IsabelleSpecial /\\<nexists>/ conceal cchar=∄
syn match IsabelleSpecial /\\<Odot>/ conceal cchar=⨀
syn match IsabelleSpecial /\\<lfloor>/ conceal cchar=⌊
syn match IsabelleSpecial /\\<sqsubset>/ conceal cchar=⊏
syn match IsabelleSpecial /\\<SS>/ conceal cchar=𝔖
syn match IsabelleSpecial /\\<box>/ conceal cchar=□
syn match IsabelleSpecial /\\<index>/ conceal cchar=ı
syn match IsabelleSpecial /\\<pounds>/ conceal cchar=£
syn match IsabelleSpecial /\\<Upsilon>/ conceal cchar=Υ
syn match IsabelleSpecial /\\<ii>/ conceal cchar=𝔦
syn match IsabelleSpecial /\\<hookleftarrow>/ conceal cchar=↩
syn match IsabelleSpecial /\\<P>/ conceal cchar=𝒫
syn match IsabelleSpecial /\\<threesuperior>/ conceal cchar=³
syn match IsabelleSpecial /\\<epsilon>/ conceal cchar=ε
syn match IsabelleSpecial /\\<yy>/ conceal cchar=𝔶
syn match IsabelleSpecial /\\<h>/ conceal cchar=𝗁
syn match IsabelleSpecial /\\<upsilon>/ conceal cchar=υ
syn match IsabelleSpecial /\\<x>/ conceal cchar=𝗑
syn match IsabelleSpecial /\\<not>/ conceal cchar=¬
syn match IsabelleSpecial /\\<le>/ conceal cchar=≤
syn match IsabelleSpecial /\\<one>/ conceal cchar=𝟭
syn match IsabelleSpecial /\\<cdots>/ conceal cchar=⋯
syn match IsabelleSpecial /\\<some>/ conceal cchar=ϵ
syn match IsabelleSpecial /\\<Prod>/ conceal cchar=∏
syn match IsabelleSpecial /\\<NN>/ conceal cchar=𝔑
syn match IsabelleSpecial /\\<squnion>/ conceal cchar=⊔
syn match IsabelleSpecial /\\<dd>/ conceal cchar=𝔡
syn match IsabelleSpecial /\\<top>/ conceal cchar=⊤
syn match IsabelleSpecial /\\<dieresis>/ conceal cchar=¨
syn match IsabelleSpecial /\\<tt>/ conceal cchar=𝔱
syn match IsabelleSpecial /\\<U>/ conceal cchar=𝒰
syn match IsabelleSpecial /\\<unlhd>/ conceal cchar=⊴
syn match IsabelleSpecial /\\<cedilla>/ conceal cchar=¸
syn match IsabelleSpecial /\\<kappa>/ conceal cchar=κ
syn match IsabelleSpecial /\\<amalg>/ conceal cchar=⨿
syn match IsabelleSpecial /\\<restriction>/ conceal cchar=↾
syn match IsabelleSpecial /\\<struct>/ conceal cchar=⋄
syn match IsabelleSpecial /\\<m>/ conceal cchar=𝗆
syn match IsabelleSpecial /\\<six>/ conceal cchar=𝟲
syn match IsabelleSpecial /\\<midarrow>/ conceal cchar=─
syn match IsabelleSpecial /\\<lbrace>/ conceal cchar=⦃
syn match IsabelleSpecial /\\<lessapprox>/ conceal cchar=⪅
syn match IsabelleSpecial /\\<MM>/ conceal cchar=𝔐
syn match IsabelleSpecial /\\<down>/ conceal cchar=↓
syn match IsabelleSpecial /\\<oplus>/ conceal cchar=⊕
syn match IsabelleSpecial /\\<wp>/ conceal cchar=℘
syn match IsabelleSpecial /\\<surd>/ conceal cchar=√
syn match IsabelleSpecial /\\<cc>/ conceal cchar=𝔠
syn match IsabelleSpecial /\\<bottom>/ conceal cchar=⊥
syn match IsabelleSpecial /\\<copyright>/ conceal cchar=©
syn match IsabelleSpecial /\\<ZZ>/ conceal cchar=ℨ
syn match IsabelleSpecial /\\<union>/ conceal cchar=∪
syn match IsabelleSpecial /\\<V>/ conceal cchar=𝒱
syn match IsabelleSpecial /\\<ss>/ conceal cchar=𝔰
syn match IsabelleSpecial /\\<unrhd>/ conceal cchar=⊵
syn match IsabelleSpecial /\\<onesuperior>/ conceal cchar=¹
syn match IsabelleSpecial /\\<b>/ conceal cchar=𝖻
syn match IsabelleSpecial /\\<downharpoonleft>/ conceal cchar=⇃
syn match IsabelleSpecial /\\<cdot>/ conceal cchar=⋅
syn match IsabelleSpecial /\\<r>/ conceal cchar=𝗋
syn match IsabelleSpecial /\\<Midarrow>/ conceal cchar=═
syn match IsabelleSpecial /\\<Down>/ conceal cchar=⇓
syn match IsabelleSpecial /\\<diamondsuit>/ conceal cchar=♢
syn match IsabelleSpecial /\\<rbrakk>/ conceal cchar=⟧
syn match IsabelleSpecial /\\<lless>/ conceal cchar=≪
syn match IsabelleSpecial /\\<longleftrightarrow>/ conceal cchar=⟷
syn match IsabelleSpecial /\\<prec>/ conceal cchar=≺
syn match IsabelleSpecial /\\<emptyset>/ conceal cchar=∅
syn match IsabelleSpecial /\\<rparr>/ conceal cchar=⦈
syn match IsabelleSpecial /\\<Delta>/ conceal cchar=Δ
syn match IsabelleSpecial /\\<XX>/ conceal cchar=𝔛
syn match IsabelleSpecial /\\<parallel>/ conceal cchar=∥
syn match IsabelleSpecial /\\<K>/ conceal cchar=𝒦
syn match IsabelleSpecial /\\<nn>/ conceal cchar=𝔫
syn match IsabelleSpecial /\\<registered>/ conceal cchar=®
syn match IsabelleSpecial /\\<M>/ conceal cchar=ℳ
syn match IsabelleSpecial /\\<delta>/ conceal cchar=δ
syn match IsabelleSpecial /\\<threequarters>/ conceal cchar=¾
syn match IsabelleSpecial /\\<g>/ conceal cchar=𝗀
syn match IsabelleSpecial /\\<cong>/ conceal cchar=≅
syn match IsabelleSpecial /\\<tau>/ conceal cchar=τ
syn match IsabelleSpecial /\\<w>/ conceal cchar=𝗐
syn match IsabelleSpecial /\\<ge>/ conceal cchar=≥
syn match IsabelleSpecial /\\<flat>/ conceal cchar=♭
syn match IsabelleSpecial /\\<zero>/ conceal cchar=𝟬
syn match IsabelleSpecial /\\<Uplus>/ conceal cchar=⨄
syn match IsabelleSpecial /\\<longmapsto>/ conceal cchar=⟼
syn match IsabelleSpecial /\\<supset>/ conceal cchar=⊃
syn match IsabelleSpecial /\\<in>/ conceal cchar=∈
syn match IsabelleSpecial /\\<sqinter>/ conceal cchar=⊓
syn match IsabelleSpecial /\\<OO>/ conceal cchar=𝔒
syn match IsabelleSpecial /\\<updown>/ conceal cchar=↕
syn match IsabelleSpecial /\\<circ>/ conceal cchar=∘
syn match IsabelleSpecial /\\<rat>/ conceal cchar=ℚ
syn match IsabelleSpecial /\\<stileturn>/ conceal cchar=⊣
syn match IsabelleSpecial /\\<ee>/ conceal cchar=𝔢
syn match IsabelleSpecial /\\<Omega>/ conceal cchar=Ω
syn match IsabelleSpecial /\\<or>/ conceal cchar=∨
syn match IsabelleSpecial /\\<inverse>/ conceal cchar=¯
syn match IsabelleSpecial /\\<rhd>/ conceal cchar=⊳
syn match IsabelleSpecial /\\<uu>/ conceal cchar=𝔲
syn match IsabelleSpecial /\\<iota>/ conceal cchar=ι
syn match IsabelleSpecial /\\<d>/ conceal cchar=𝖽
syn match IsabelleSpecial /\\<questiondown>/ conceal cchar=¿
syn match IsabelleSpecial /\\<Union>/ conceal cchar=⋃
syn match IsabelleSpecial /\\<omega>/ conceal cchar=ω
syn match IsabelleSpecial /\\<approx>/ conceal cchar=≈
syn match IsabelleSpecial /\\<t>/ conceal cchar=𝗍
syn match IsabelleSpecial /\\<Updown>/ conceal cchar=⇕
syn match IsabelleSpecial /\\<spadesuit>/ conceal cchar=♠
syn match IsabelleSpecial /\\<five>/ conceal cchar=𝟱
syn match IsabelleSpecial /\\<exists>/ conceal cchar=∃
syn match IsabelleSpecial /\\<rceil>/ conceal cchar=⌉
syn match IsabelleSpecial /\\<JJ>/ conceal cchar=𝔍
syn match IsabelleSpecial /\\<minusplus>/ conceal cchar=∓
syn match IsabelleSpecial /\\<nat>/ conceal cchar=ℕ
syn match IsabelleSpecial /\\<oslash>/ conceal cchar=⊘
syn match IsabelleSpecial /\\<A>/ conceal cchar=𝒜
syn match IsabelleSpecial /\\<Xi>/ conceal cchar=Ξ
syn match IsabelleSpecial /\\<currency>/ conceal cchar=¤
syn match IsabelleSpecial /\\<Turnstile>/ conceal cchar=⊨
syn match IsabelleSpecial /\\<hookrightarrow>/ conceal cchar=↪
syn match IsabelleSpecial /\\<pp>/ conceal cchar=𝔭
syn match IsabelleSpecial /\\<Q>/ conceal cchar=𝒬
syn match IsabelleSpecial /\\<aleph>/ conceal cchar=ℵ
syn match IsabelleSpecial /\\<acute>/ conceal cchar=´
syn match IsabelleSpecial /\\<xi>/ conceal cchar=ξ
syn match IsabelleSpecial /\\<simeq>/ conceal cchar=≃
syn match IsabelleSpecial /\\<i>/ conceal cchar=𝗂
syn match IsabelleSpecial /\\<Join>/ conceal cchar=⋈
syn match IsabelleSpecial /\\<y>/ conceal cchar=𝗒
syn match IsabelleSpecial /\\<lbrakk>/ conceal cchar=⟦
syn match IsabelleSpecial /\\<greatersim>/ conceal cchar=≳
syn match IsabelleSpecial /\\<greaterapprox>/ conceal cchar=⪆
syn match IsabelleSpecial /\\<longrightarrow>/ conceal cchar=⟶
syn match IsabelleSpecial /\\<lceil>/ conceal cchar=⌈
syn match IsabelleSpecial /\\<Gamma>/ conceal cchar=Γ
syn match IsabelleSpecial /\\<odot>/ conceal cchar=⊙
syn match IsabelleSpecial /\\<YY>/ conceal cchar=𝔜
syn match IsabelleSpecial /\\<infinity>/ conceal cchar=∞
syn match IsabelleSpecial /\\<Sigma>/ conceal cchar=Σ
syn match IsabelleSpecial /\\<yen>/ conceal cchar=¥
syn match IsabelleSpecial /\\<int>/ conceal cchar=ℤ
syn match IsabelleSpecial /\\<tturnstile>/ conceal cchar=⊩
syn match IsabelleSpecial /\\<oo>/ conceal cchar=𝔬
syn match IsabelleSpecial /\\<ointegral>/ conceal cchar=∮
syn match IsabelleSpecial /\\<gamma>/ conceal cchar=γ
syn match IsabelleSpecial /\\<upharpoonleft>/ conceal cchar=↿
syn match IsabelleSpecial /\\<sigma>/ conceal cchar=σ
syn match IsabelleSpecial /\\<n>/ conceal cchar=𝗇
syn match IsabelleSpecial /\\<rbrace>/ conceal cchar=⦄
syn match IsabelleSpecial /\\<DD>/ conceal cchar=𝔇
syn match IsabelleSpecial /\\<notin>/ conceal cchar=∉
syn match IsabelleSpecial /\\<j>/ conceal cchar=𝗃
syn match IsabelleSpecial /\\<uplus>/ conceal cchar=⊎
syn match IsabelleSpecial /\\<leftrightarrow>/ conceal cchar=↔
syn match IsabelleSpecial /\\<TT>/ conceal cchar=𝔗
syn match IsabelleSpecial /\\<bullet>/ conceal cchar=∙
syn match IsabelleSpecial /\\<Theta>/ conceal cchar=Θ
syn match IsabelleSpecial /\\<smile>/ conceal cchar=⌣
syn match IsabelleSpecial /\\<G>/ conceal cchar=𝒢
syn match IsabelleSpecial /\\<jj>/ conceal cchar=𝔧
syn match IsabelleSpecial /\\<inter>/ conceal cchar=∩
syn match IsabelleSpecial /\\<Psi>/ conceal cchar=Ψ
syn match IsabelleSpecial /\\<ordfeminine>/ conceal cchar=ª
syn match IsabelleSpecial /\\<W>/ conceal cchar=𝒲
syn match IsabelleSpecial /\\<zz>/ conceal cchar=𝔷
syn match IsabelleSpecial /\\<theta>/ conceal cchar=θ
syn match IsabelleSpecial /\\<ordmasculine>/ conceal cchar=º
syn match IsabelleSpecial /\\<c>/ conceal cchar=𝖼
syn match IsabelleSpecial /\\<psi>/ conceal cchar=ψ
syn match IsabelleSpecial /\\<s>/ conceal cchar=𝗌
syn match IsabelleSpecial /\\<Leftrightarrow>/ conceal cchar=⇔
syn match IsabelleSpecial /\\<heartsuit>/ conceal cchar=♡
syn match IsabelleSpecial /\\<four>/ conceal cchar=𝟰
syn match IsabelleSpecial /\\<open>/ conceal cchar=‹ transparent
syn match IsabelleSpecial /\\<close>/ conceal cchar=› transparent
syn match IsabelleSpecial /\\<comment>/ conceal cchar=— transparent

syn cluster IsabelleInnerStuff contains=IsabelleSpecial,IsabelleComment

" Enable folding of proofs and locales. Note that the starting regex needs to
" match with zero width to preserve syntax highlighting of the opening command.
syn region IsabelleLemmaFold
    \ start="\(\<\(schematic_\)\?\(corollary\|lemma\|theorem\)\>\|have\|show\)\@<="
    \ end="\<\(done\|by\|qed\|apply_end\|oops\|sorry\)\>"
    \ fold keepend transparent
syn region IsabelleLocaleFold
    \ start="\(\<\(sub\)\?locale\>\)\@<="
    \ end="\<end\>"
    \ fold keepend transparent

syn match IsabelleComment "--.*$"
hi def link IsabelleComment Comment
hi def link IsabelleCommentStart Comment
hi def link IsabelleCommentContent Comment

hi IsabelleCommand           ctermfg=3 cterm=bold guifg=yellow gui=bold
hi IsabelleCommandPart       ctermfg=3 cterm=none guifg=yellow
hi IsabelleCommandMod        ctermfg=3 cterm=none guifg=yellow
hi IsabelleInnerMarker       ctermfg=1 cterm=none guifg=red
hi IsabelleSpecial           ctermfg=5 cterm=none guifg=magenta
hi IsabelleCommandProofProve ctermfg=2 cterm=none guifg=green
hi IsabelleCommandProofIsar  ctermfg=2 cterm=none guifg=green
hi IsabelleGoalProofIsar     ctermfg=3 cterm=none guifg=yellow
hi IsabelleCommandProofDone  ctermfg=2 cterm=bold guifg=green gui=bold
hi IsabelleCommandProofFail  ctermfg=1 cterm=bold guifg=red   gui=bold
hi IsabelleCommandProofBad   ctermfg=1 cterm=none guifg=red
hi IsabelleCommandRule       ctermfg=7 cterm=bold guifg=white gui=bold
hi IsabelleCommandRuleMod    ctermfg=6 cterm=none guifg=cyan
hi IsabelleCommandMethod     ctermfg=6 cterm=none guifg=cyan
hi IsabelleCommandMethodMod  ctermfg=6 cterm=none guifg=cyan
hi IsabelleCommandBigMethod  ctermfg=6 cterm=bold guifg=cyan gui=bold

hi Normal guibg=black guifg=grey

" Jedit-style autocompletion. This is off by default because it can
" significantly slow Vim down. To use this functionality, put something like
" the following in your ~/.vimrc and then use F9 to toggle completion on and
" off.
"
"     function! ToggleIsabelleAbbreviations()
"       if exists('g:isabelle_abbreviations')
"         let g:isabelle_abbreviations=!g:isabelle_abbreviations
"       else
"         let g:isabelle_abbreviations=1
"       endif
"       syntax off
"       syntax on
"     endfunction
"     nm <F9> :call ToggleIsabelleAbbreviations()<CR>
"     imap <F9> <C-o>:call ToggleIsabelleAbbreviations()<CR>
"
if exists('g:isabelle_abbreviations')
  if g:isabelle_abbreviations == 1
    " Tweak the things that Vim sees as part of a word. This is useful if you
    " have macros that kick in on word completion or similar.
    set iskeyword+=>
    set iskeyword+=]
    set iskeyword+=:
    " XXX: Vim does not seem to have a way to add '*' to the iskeyword set.

    " Jedit-style autocomplete of unicode tokens. This was generated by the
    " following Python
    "
    "     import isasymbols # From l4v-internal
    "
    "     def vim_escape(data):
    "         'Escape characters that are special to Vim'
    "         return data.replace('<', '<lt>').replace('\\',
    "             '<Bslash>').replace('|', '<Bar>')
    "
    "     t = isasymbols.make_translator('/path/to/symbols')
    "     for symbol in t.symbols:
    "         for abbreviation in symbol.abbreviations:
    "             print 'iab %s %s' % (vim_escape(abbreviation),
    "                 vim_escape(symbol.ascii_text))
    "
    iab <buffer> % <Bslash><lt>lambda>
    iab <buffer> <lt>. <Bslash><lt>leftarrow>
    iab <buffer> <lt>. <Bslash><lt>longleftarrow>
    iab <buffer> .> <Bslash><lt>rightarrow>
    iab <buffer> -> <Bslash><lt>rightarrow>
    iab <buffer> .> <Bslash><lt>longrightarrow>
    iab <buffer> --> <Bslash><lt>longrightarrow>
    iab <buffer> <lt>. <Bslash><lt>Leftarrow>
    iab <buffer> <lt>. <Bslash><lt>Longleftarrow>
    iab <buffer> .> <Bslash><lt>Rightarrow>
    iab <buffer> => <Bslash><lt>Rightarrow>
    iab <buffer> .> <Bslash><lt>Longrightarrow>
    iab <buffer> ==> <Bslash><lt>Longrightarrow>
    iab <buffer> <lt>> <Bslash><lt>leftrightarrow>
    iab <buffer> <lt>-> <Bslash><lt>leftrightarrow>
    iab <buffer> <lt>> <Bslash><lt>longleftrightarrow>
    iab <buffer> <lt>-> <Bslash><lt>longleftrightarrow>
    iab <buffer> <lt>--> <Bslash><lt>longleftrightarrow>
    iab <buffer> <lt>> <Bslash><lt>Leftrightarrow>
    iab <buffer> <lt>> <Bslash><lt>Longleftrightarrow>
    iab <buffer> .> <Bslash><lt>mapsto>
    iab <buffer> <Bar>-> <Bslash><lt>mapsto>
    iab <buffer> .> <Bslash><lt>longmapsto>
    iab <buffer> <Bar>--> <Bslash><lt>longmapsto>
    iab <buffer> <lt>> <Bslash><lt>midarrow>
    iab <buffer> <lt>> <Bslash><lt>Midarrow>
    iab <buffer> <lt>. <Bslash><lt>hookleftarrow>
    iab <buffer> .> <Bslash><lt>hookrightarrow>
    iab <buffer> <lt>. <Bslash><lt>leftharpoondown>
    iab <buffer> .> <Bslash><lt>rightharpoondown>
    iab <buffer> <lt>. <Bslash><lt>leftharpoonup>
    iab <buffer> .> <Bslash><lt>rightharpoonup>
    iab <buffer> <lt>> <Bslash><lt>rightleftharpoons>
    iab <buffer> == <Bslash><lt>rightleftharpoons>
    iab <buffer> .> <Bslash><lt>leadsto>
    iab <buffer> ~> <Bslash><lt>leadsto>
    iab <buffer> <lt><lt> <Bslash><lt>langle>
    iab <buffer> >> <Bslash><lt>rangle>
    iab <buffer> [. <Bslash><lt>lceil>
    iab <buffer> .] <Bslash><lt>rceil>
    iab <buffer> [. <Bslash><lt>lfloor>
    iab <buffer> .] <Bslash><lt>rfloor>
    iab <buffer> (<Bar> <Bslash><lt>lparr>
    iab <buffer> <Bar>) <Bslash><lt>rparr>
    iab <buffer> [<Bar> <Bslash><lt>lbrakk>
    iab <buffer> <Bar>] <Bslash><lt>rbrakk>
    iab <buffer> {<Bar> <Bslash><lt>lbrace>
    iab <buffer> <Bar>} <Bslash><lt>rbrace>
    iab <buffer> <lt><lt> <Bslash><lt>guillemotleft>
    iab <buffer> >> <Bslash><lt>guillemotright>
    iab <buffer> /<Bslash> <Bslash><lt>and>
    iab <buffer> & <Bslash><lt>and>
    iab <buffer> !! <Bslash><lt>And>
    iab <buffer> <Bslash>/ <Bslash><lt>or>
    iab <buffer> <Bar> <Bslash><lt>or>
    iab <buffer> ?? <Bslash><lt>Or>
    iab <buffer> ! <Bslash><lt>forall>
    iab <buffer> ALL <Bslash><lt>forall>
    iab <buffer> ? <Bslash><lt>exists>
    iab <buffer> EX <Bslash><lt>exists>
    iab <buffer> ~? <Bslash><lt>nexists>
    iab <buffer> ~ <Bslash><lt>not>
    iab <buffer> <Bar>- <Bslash><lt>turnstile>
    iab <buffer> <Bar>= <Bslash><lt>Turnstile>
    iab <buffer> <Bar>- <Bslash><lt>tturnstile>
    iab <buffer> <Bar>= <Bslash><lt>TTurnstile>
    iab <buffer> -<Bar> <Bslash><lt>stileturn>
    iab <buffer> <lt>= <Bslash><lt>le>
    iab <buffer> >= <Bslash><lt>ge>
    iab <buffer> <lt><lt> <Bslash><lt>lless>
    iab <buffer> >> <Bslash><lt>ggreater>
    iab <buffer> : <Bslash><lt>in>
    iab <buffer> ~: <Bslash><lt>notin>
    iab <buffer> (= <Bslash><lt>subseteq>
    iab <buffer> )= <Bslash><lt>supseteq>
    iab <buffer> [= <Bslash><lt>sqsubseteq>
    iab <buffer> ]= <Bslash><lt>sqsupseteq>
    iab <buffer> Int <Bslash><lt>inter>
    iab <buffer> Inter <Bslash><lt>Inter>
    iab <buffer> INT <Bslash><lt>Inter>
    iab <buffer> Un <Bslash><lt>union>
    iab <buffer> Union <Bslash><lt>Union>
    iab <buffer> UN <Bslash><lt>Union>
    iab <buffer> SUP <Bslash><lt>Squnion>
    iab <buffer> INF <Bslash><lt>Sqinter>
    iab <buffer> ~= <Bslash><lt>noteq>
    iab <buffer> .= <Bslash><lt>doteq>
    iab <buffer> == <Bslash><lt>equiv>
    iab <buffer> <Bar><Bar> <Bslash><lt>parallel>
    iab <buffer> <Bar><Bar> <Bslash><lt>bar>
    iab <buffer> <lt>*> <Bslash><lt>times>
    iab <buffer> +o <Bslash><lt>oplus>
    iab <buffer> +O <Bslash><lt>Oplus>
    iab <buffer> *o <Bslash><lt>otimes>
    iab <buffer> *O <Bslash><lt>Otimes>
    iab <buffer> .o <Bslash><lt>odot>
    iab <buffer> .O <Bslash><lt>Odot>
    iab <buffer> -o <Bslash><lt>ominus>
    iab <buffer> /o <Bslash><lt>oslash>
    iab <buffer> ... <Bslash><lt>dots>
    iab <buffer> SUM <Bslash><lt>Sum>
    iab <buffer> PROD <Bslash><lt>Prod>
    iab <buffer> <lt><lt> <Bslash><lt>open>
    iab <buffer> >> <Bslash><lt>close>
    iab <buffer> =_( <Bslash><lt>^bsub>
    iab <buffer> =_) <Bslash><lt>^esub>
    iab <buffer> =^( <Bslash><lt>^bsup>
    iab <buffer> =^) <Bslash><lt>^esup>
  else
    " Reset to default.
    set iskeyword=@,48-57,_,192-255

    " Remove all abbreviations.
    iabc <buffer>
  endif
endif

"" End seL4/isabelle code

" These colors were adapted from the light mode colors of the official VSCode
" extension.

hi default IsaDecorationBackgroundUnprocessed ctermbg=217
hi default IsaDecorationBackgroundUnprocessed1 ctermbg=217
hi default IsaDecorationBackgroundRunning ctermbg=53
hi default IsaDecorationBackgroundRunning1 ctermbg=53
hi default IsaDecorationBackgroundCanceled ctermbg=203
hi default IsaDecorationBackgroundBad ctermbg=203
hi default IsaDecorationBackgroundIntensify ctermbg=221
hi default IsaDecorationBackgroundMarkdownBullet1 ctermbg=194
hi default IsaDecorationBackgroundMarkdownBullet2 ctermbg=230
hi default IsaDecorationBackgroundMarkdownBullet3 ctermbg=189
hi default IsaDecorationBackgroundMarkdownBullet4 ctermbg=225
hi default IsaDecorationForegroundQuoted ctermbg=254
hi default IsaDecorationForegroundAntiquoted ctermbg=221
hi default IsaDecorationDottedWriteln ctermfg=145 cterm=underline
hi default IsaDecorationDottedInformation ctermfg=153 cterm=underline
hi default IsaDecorationDottedWarning ctermfg=208 cterm=underline
hi default IsaDecorationTextError ctermfg=124
hi default IsaDecorationTextSpellChecker ctermfg=21
hi default IsaDecorationTextMain ctermfg=16
hi default IsaDecorationTextKeyword1 ctermfg=128
hi default IsaDecorationTextKeyword2 ctermfg=29
hi default IsaDecorationTextKeyword3 ctermfg=30
hi default IsaDecorationTextQuasiKeyword ctermfg=99
hi default IsaDecorationTextImproper ctermfg=167
hi default IsaDecorationTextOperator ctermfg=59
hi default IsaDecorationTextTfree ctermfg=129
hi default IsaDecorationTextTvar ctermfg=129
hi default IsaDecorationTextFree ctermfg=21
hi default IsaDecorationTextSkolem ctermfg=166
hi default IsaDecorationTextBound ctermfg=28
hi default IsaDecorationTextVar ctermfg=18
hi default IsaDecorationTextInnerNumeral ctermfg=29
hi default IsaDecorationTextInnerQuoted ctermfg=124
hi default IsaDecorationTextInnerCartouche ctermfg=89
hi default IsaDecorationTextInnerComment ctermfg=28
hi default IsaDecorationTextComment1 ctermfg=89
hi default IsaDecorationTextComment2 ctermfg=167
hi default IsaDecorationTextComment3 ctermfg=28
hi default IsaDecorationTextDynamic ctermfg=94
hi default IsaDecorationTextClassParameter ctermfg=166
hi default IsaDecorationTextAntiquote ctermfg=56
hi default IsaDecorationTextRawText ctermfg=56
hi default IsaDecorationTextPlainText ctermfg=56

"TODO: Overview colors
"hi default IsaDecorationTextOverviewUnprocessed ctermfg=217
"hi default IsaDecorationTextOverviewRunning ctermfg=53
"hi default IsaDecorationTextOverviewError ctermfg=124
"hi default IsaDecorationTextOverviewWarning ctermfg=208
