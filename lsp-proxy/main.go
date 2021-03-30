package main

import (
	"bytes"
	"context"
	"encoding/json"
	"fmt"
	"io"
	"log"
	"os"
	"os/exec"
	"regexp"
	"strings"
	"sync"

	"github.com/neovim/go-client/nvim"
	"go.lsp.dev/jsonrpc2"
)

const (
	Error = 1 + iota
	Warning
	Information
	Hint
)

var n *nvim.Nvim
var isaOutputBuffer nvim.Buffer

type Position struct {
	Line      int `json:"line"`
	Character int `json:"character"`
}

type Diagnostic struct {
	JsonRpc  string `json:"jsonrpc"` // must be "2.0"
	Source   string `json:"source,omitempty"`
	Severity int    `json:"severity,omitempty"`
	Range    Range  `json:"range"`
	Msg      string `json:"message"`
}

type Capabilities struct {
	DefinitionProvider        bool        `json:"definitionProvider"`
	HoverProvider             bool        `json:"hoverProvider"`
	CompletionProvider        interface{} `json:"completionProvider"`
	DocumentHighlightProvider bool        `json:"documentHighlightProvider"`
	CodeActionProvider        bool        `json:"codeActionProvider"`
	TextDocumentSync          int         `json:"textDocumentSync"`
}

type PublishDiagnostics struct {
	Uri         string       `json:"uri"`
	Diagnostics []Diagnostic `json:"diagnostics"`
}

type Range struct {
	Start Position `json:"start"`
	End   Position `json:"end"`
}

type PIDERange struct {
	Range [4]int `json:"range"`
}

type TextEdit struct {
	Range   Range  `json:"range"`
	NewText string `json:"newText"`
}

type WorkspaceEdit struct {
	Changes map[string][]TextEdit `json:"changes"`
}

type CodeAction struct {
	Title         string        `json:"title"`
	Kind          string        `json:"kind"`
	WorkspaceEdit WorkspaceEdit `json:"edit"`
}

type stub struct {
	r io.Reader
	w io.Writer
}

func (s stub) Read(p []byte) (int, error) {
	return s.r.Read(p)
}

func (s stub) Write(p []byte) (int, error) {
	return s.w.Write(p)
}

func (s stub) Close() error {
	var err1, err2 error
	if c, ok := s.r.(io.Closer); ok {
		err1 = c.Close()
	}

	if c, ok := s.w.(io.Closer); ok {
		err2 = c.Close()
	}

	if err1 != nil {
		return err1
	}
	return err2
}

type stream struct {
	s jsonrpc2.Stream
	l *sync.Mutex
}

func (s stream) Read(ctx context.Context) (jsonrpc2.Message, int64, error) {
	return s.s.Read(ctx)
}

func (s stream) Write(ctx context.Context, msg jsonrpc2.Message) (int64, error) {
	s.l.Lock()
	defer s.l.Unlock()
	return s.s.Write(ctx, msg)
}

func main() {
	f, err := os.OpenFile("/tmp/loggggg", os.O_RDWR|os.O_CREATE|os.O_APPEND, 0640)
	if err != nil {
		log.Fatal(err)
	}
	log.SetOutput(f)

	args := os.Args
	if len(args) < 2 {
		log.Fatalf("expected argument: %s <nvim-socket>", os.Args[0])
	}
	socket := args[1]
	log.Printf("socket: %s", socket)

	n, err = nvim.Dial(socket)
	if err != nil {
		log.Fatal(err)
	}

	args = []string{"vscode_server", "-v", "-L", "/tmp/go-isa-lsp"}
	cmd := exec.Command("isabelle", append(args, os.Args[2:]...)...)
	lspin, err := cmd.StdinPipe()
	if err != nil {
		log.Fatal(err)
	}

	lspout, err := cmd.StdoutPipe()
	if err != nil {
		log.Fatal(err)
	}

	go func() { cmd.Run() }()

	server := stream{
		s: jsonrpc2.NewStream(stub{r: os.Stdin, w: os.Stdout}),
		l: &sync.Mutex{},
	}
	client := stream{
		s: jsonrpc2.NewStream(stub{r: lspout, w: lspin}),
		l: &sync.Mutex{},
	}

	handleCommands(server, client)
}

func sendUpdateCaret(s stream) func([]interface{}) {
	return func(args []interface{}) {
		uri := args[0].(string)
		line := args[1].(int)
		col := args[2].(int)

		type params struct {
			Uri  string `json:"uri"`
			Line int    `json:"line"`
			Col  int    `json:"character"`
		}
		n, err := jsonrpc2.NewNotification("PIDE/caret_update", params{Uri: uri, Line: line, Col: col})
		if err != nil {
			log.Fatal(err)
		}

		log.Printf("writing caret update: %d %d", line, col)
		_, err = s.s.Write(context.TODO(), n)
		if err != nil {
			log.Fatal(err)
		}
	}
}

func proxyToIsabelleHandler(next proxy, nv stream) proxy {
	return func(to stream, msg jsonrpc2.Message) {
		switch msg.(type) {
		case *jsonrpc2.Notification:
			next(to, msg)
		case *jsonrpc2.Call:
			c := msg.(*jsonrpc2.Call)
			switch c.Method() {
			case "textDocument/codeAction":
				log.Println("got codeAction, not forwarding")

				var params struct {
					Range        Range `json:"range"`
					TextDocument struct {
						Uri string `json:"uri"`
					} `json:"textDocument"`
				}
				j, err := c.Params().MarshalJSON()
				if err != nil {
					log.Fatal(err)
				}
				err = json.Unmarshal(j, &params)
				if err != nil {
					log.Fatal(err)
				}
				if params.Range.Start.Line != params.Range.End.Line {
					return
				}

				isaBuffer, err := n.BufferLines(isaOutputBuffer, 0, -1, false)
				if err != nil {
					log.Fatal(err)
				}

				fix := ""
				for _, line := range isaBuffer {
					line := string(line)
					if strings.HasPrefix(line, "Try this: ") {
						fix = strings.TrimPrefix(line, "Try this: ")
						break
					}
				}

				if fix == "" {
					return
				}

				r := regexp.MustCompile(` *\([0-9]+ ms\)`)
				fix = r.ReplaceAllString(fix, "")

				a := []CodeAction{{
					Kind: "quickfix",
					WorkspaceEdit: WorkspaceEdit{
						Changes: map[string][]TextEdit{
							params.TextDocument.Uri: {
								{
									NewText: fix,
									Range: Range{
										Start: Position{
											Line: params.Range.Start.Line,
										},
										End: Position{
											Line: params.Range.Start.Line,
										},
									},
								},
							},
						},
					},
				}}

				linebarr, err := n.CurrentLine()
				if err != nil {
					log.Panic(err)
				}
				line := string(linebarr)

				var origin string
				if strings.Contains(line, "try0") {
					origin = "try0"
					ind := strings.LastIndex(line, "try0")
					a[0].WorkspaceEdit.Changes[params.TextDocument.Uri][0].Range.Start.Character = ind
					a[0].WorkspaceEdit.Changes[params.TextDocument.Uri][0].Range.End.Character = ind + 4
				} else if strings.Contains(line, "try") {
					origin = "try"
					ind := strings.LastIndex(line, "try")
					a[0].WorkspaceEdit.Changes[params.TextDocument.Uri][0].Range.Start.Character = ind
					a[0].WorkspaceEdit.Changes[params.TextDocument.Uri][0].Range.End.Character = ind + 3
				} else if strings.Contains(line, "sledgehammer") {
					origin = "sledgehammer"
					ind := strings.LastIndex(line, "sledgehammer")
					a[0].WorkspaceEdit.Changes[params.TextDocument.Uri][0].Range.Start.Character = ind
					a[0].WorkspaceEdit.Changes[params.TextDocument.Uri][0].Range.End.Character = ind + 12
				} else {
					return
				}

				a[0].Title = fmt.Sprintf("Replace '%s' with '%s'", origin, fix)

				resp, err := jsonrpc2.NewResponse(c.ID(), a, nil)
				if err != nil {
					log.Fatal(err)
				}

				log.Printf("debug resp: %v", string(resp.Result()))

				_, err = nv.Write(context.TODO(), resp)
				if err != nil {
					log.Fatal(err)
				}
			default:
				next(to, msg)
			}
		case *jsonrpc2.Response:
			next(to, msg)
		default:
			log.Printf("unknown message type %T", msg)
		}
	}
}

func proxyIsabelleHandler(next proxy) proxy {
	return func(to stream, msg jsonrpc2.Message) {
		switch msg.(type) {
		case *jsonrpc2.Notification:
			c := msg.(*jsonrpc2.Notification)
			switch c.Method() {
			case "PIDE/dynamic_output":
				log.Printf("got dynamic output")
				// write into scratch buffer
				var params struct {
					Content string `json:"content"`
				}
				j, err := c.Params().MarshalJSON()
				if err != nil {
					log.Fatal(err)
				}
				err = json.Unmarshal(j, &params)
				if err != nil {
					log.Fatal(err)
				}
				err = n.SetBufferLines(isaOutputBuffer, 0, -1, false, bytes.Split([]byte(params.Content), []byte{'\n'}))
				if err != nil {
					log.Fatal(err)
				}
			case "PIDE/decoration":
				log.Printf("got decoration")
				// write into scratch buffer
				handleDecorationRequest(c)
			default:
				next(to, msg)
			}
		case *jsonrpc2.Call:
			next(to, msg)
		case *jsonrpc2.Response:
			r := msg.(*jsonrpc2.Response)
			switch r.ID() {
			case jsonrpc2.NewNumberID(0): // assume this is the response to initialize
				log.Print("intercepted initial response")
				var result struct {
					Capabilities Capabilities `json:"capabilities"`
				}
				j, err := r.Result().MarshalJSON()
				if err != nil {
					log.Fatal(err)
				}
				err = json.Unmarshal(j, &result)
				if err != nil {
					log.Fatal(err)
				}
				result.Capabilities.CodeActionProvider = true
				r, err := jsonrpc2.NewResponse(r.ID(), result, nil)
				if err != nil {
					log.Fatal(err)
				}
				_, err = to.Write(context.TODO(), r)
				if err != nil {
					log.Fatal(err)
				}
			default:
				next(to, msg)
			}
		default:
			log.Printf("unknown message type %T", msg)
		}
	}
}

func getBufferWithName(name string) nvim.Buffer {
	var bufnr int
	err := n.Call("bufnr", &bufnr, []string{name})
	if err != nil {
		log.Fatal(err)
	}
	if bufnr <= 0 {
		log.Fatal("bufnr is <= 0, buf not found")
	}
	return nvim.Buffer(bufnr)
}

func handleCommands(vim, isa stream) {
	isaOutputBuffer = getBufferWithName("-OUTPUT-")
	log.Println("created temp buffer")

	n.RegisterHandler("send_caret_update", sendUpdateCaret(isa))

	// TODO: attach to cursorMoved in

	go runProxy(vim, isa, proxyToIsabelleHandler(proxyLSP, vim))
	runProxy(isa, vim, proxyIsabelleHandler(proxyLSP))
}

type proxy func(stream, jsonrpc2.Message)

func proxyLSP(to stream, msg jsonrpc2.Message) {
	_, err := to.s.Write(context.TODO(), msg)
	if err != nil {
		log.Fatal(err)
	}
}

func runProxy(from, to stream, p proxy) {
	for {
		msg, _, err := from.s.Read(context.TODO())
		if err != nil {
			log.Fatal(err)
		}
		p(to, msg)
	}
}
