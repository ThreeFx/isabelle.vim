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

function! s:isa_output_window()
	let bnr = bufwinnr('-OUTPUT-')
	if bnr == -1
		noautocmd execute 'silent! belowright ' . g:isabelle_output_height . ' split -OUTPUT-'
		setlocal buftype=nofile
		setlocal bufhidden=hide
		setlocal noswapfile nobuflisted textwidth=0
		setlocal nolist winfixheight nospell nowrap nonumber nocursorline
		wincmd p
	endif
endfunction

function! s:isa_progress_window()
	let bnr = bufwinnr('-PROGRESS-')
	if bnr == -1
		noautocmd execute 'silent! belowright ' . g:isabelle_progress_width . ' vsplit -PROGRESS-'
		setlocal buftype=nofile
		setlocal bufhidden=hide
		setlocal noswapfile nobuflisted textwidth=0
		setlocal nolist winfixwidth nospell nowrap nonumber nocursorline
		wincmd p
	endif
endfunction

function! s:try_close()
	if !exists('g:isabelle_vim_close')
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
	endif
endfunction

command! IsabelleWindow call s:isa_output_window()|call s:isa_progress_window()

augroup isabelle_vim
	au!
	au FileType isabelle IsabelleWindow
	au QuitPre * let g:isabelle_vim_close=1
	au WinEnter * call s:try_close()
augroup END
