if exists('g:loaded_isabelle_vim')
	finish
endif
let g:loaded_isabelle_vim = 1

if !exists('g:isabelle_progress_width')
	let g:isabelle_progress_width = 40 
endif

if !exists('g:isabelle_output_height')
	let g:isabelle_output_height = 10
endif

function! s:open_isa_output_window()
	let bnr = bufwinnr('-OUTPUT-')
	if bnr == -1
		noautocmd execute 'silent! belowright ' . g:isabelle_output_height . ' split -OUTPUT-'
		setlocal buftype=nofile
		setlocal bufhidden=hide
		setlocal filetype=isabelle
		setlocal noswapfile nobuflisted textwidth=0
		setlocal nolist winfixheight nospell wrap nonumber nocursorline
		wincmd p
	endif
endfunction

function! s:close_window(arg)
	let wnr = bufwinnr(a:arg)
	if wnr > 0
		execute wnr . ' wincmd c'
	endif
endfunction

function! s:open_isa_progress_window()
	let bnr = bufwinnr('-PROGRESS-')
	if bnr == -1
		noautocmd execute 'silent! belowright ' . g:isabelle_progress_width . ' vsplit -PROGRESS-'
		setlocal buftype=nofile
		setlocal bufhidden=hide
		setlocal noswapfile nobuflisted textwidth=0
		setlocal nolist winfixwidth nospell wrap nonumber nocursorline
		wincmd p
	endif
endfunction

function! s:toggle_windows()
	let bnr = bufwinnr('-PROGRESS-')
	if bnr > 0
		execute 'CloseIsabelleWindows'
	else
		execute 'OpenIsabelleWindows'
	endif
endfunction

function! s:try_quit()
	if !exists('g:isabelle_vim_close') || g:isabelle_vim_close == 0
		return
	endif
	let cnt = 0
	let l = ['-MINIMAP-', '-PROGRESS-', '-OUTPUT-']
	for bufn in l
		if bufnr(bufn) > 0
			let cnt += 1
		endif
	endfor
	let wnr = winnr('$')
	if wnr == cnt
		doautocmd ExitPre,VimLeavePre,VimLeave
		execute 'qa'
	else
		let g:isabelle_vim_close = 0
	endif
endfunction

command! OpenIsabelleWindows call s:open_isa_progress_window()|call s:open_isa_output_window()
command! CloseIsabelleWindows call s:close_window('-PROGRESS-')|call s:close_window('-OUTPUT-')
command! ToggleIsabelleWindows call s:toggle_windows()

augroup isabelle_vim
	au!
	au FileType isabelle OpenIsabelleWindows
	au QuitPre * let g:isabelle_vim_close=1
	au WinEnter * call s:try_quit()
augroup END
