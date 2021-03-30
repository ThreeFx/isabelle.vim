package main

import (
	"encoding/json"
	"log"
	"regexp"
	"strings"
	"sync"

	"go.lsp.dev/jsonrpc2"
)

var hlcMu = &sync.Mutex{}
var highlightCache = make(map[string]map[string]map[Range]struct{})

func extractPayload(m jsonrpc2.Message, payload interface{}) {
	var j json.RawMessage
	var err error
	switch m.(type) {
	case *jsonrpc2.Notification:
		j, err = m.(*jsonrpc2.Notification).Params().MarshalJSON()
		if err != nil {
			log.Fatal(err)
		}
	case *jsonrpc2.Call:
		j, err = m.(*jsonrpc2.Call).Params().MarshalJSON()
		if err != nil {
			log.Fatal(err)
		}
	case *jsonrpc2.Response:
		j, err = m.(*jsonrpc2.Response).Result().MarshalJSON()
		if err != nil {
			log.Fatal(err)
		}
	}
	err = json.Unmarshal(j, &payload)
	if err != nil {
		log.Fatal(err)
	}
}

func handleDecorationRequest(m jsonrpc2.Message) {
	var params struct {
		Uri     string      `json:"uri"`
		Type    string      `json:"type"`
		Content []PIDERange `json:"content"`
	}
	extractPayload(m, &params)

	bufNr := getBufferWithName(strings.TrimPrefix(params.Uri, "file://"))

	hlcMu.Lock()
	mp, ok := highlightCache[params.Uri]
	if !ok {
		mp = make(map[string]map[Range]struct{})
	}
	dm, ok := mp[params.Type]
	if !ok {
		dm = make(map[Range]struct{})
	}

	newKeys := make(map[Range]struct{})
	toClear := make(map[Range]struct{})
	toAdd := make(map[Range]struct{})
	for _, r := range params.Content {
		start := Position{Line: r.Range[0], Character: r.Range[1]}
		end := Position{Line: r.Range[2], Character: r.Range[3]}
		rr := Range{start, end}

		newKeys[rr] = struct{}{}
		if _, exists := dm[rr]; !exists {
			toAdd[rr] = struct{}{}
			toClear[rr] = struct{}{}
		}
	}

	for k := range dm {
		if _, exists := newKeys[k]; !exists {
			toClear[k] = struct{}{}
		}
	}

	highlightCache[params.Uri][params.Type] = newKeys
	hlcMu.Unlock()

	for k := range toClear {
		n.Call("nvim_buf_clear_namespace", nil, bufNr, params.Type, k.Start.Line, k.End.Line+1)
	}

	hlGroup := toVimHlGroup(params.Type)
	for k := range toAdd {
		if k.Start.Line == k.End.Line {
			n.Call("nvim_buf_add_highlight", nil, bufNr, params.Type, hlGroup, k.Start.Line, k.Start.Character, k.End.Character)
		} else {
			n.Call("nvim_buf_add_highlight", nil, bufNr, params.Type, hlGroup, k.Start.Line, k.Start.Character, -1)
			n.Call("nvim_buf_add_highlight", nil, bufNr, params.Type, hlGroup, k.End.Line, 0, k.End.Character)
			for line := k.Start.Line + 1; line < k.End.Line; line++ {
				n.Call("nvim_buf_add_highlight", nil, bufNr, params.Type, hlGroup, line, 0, -1)
			}
		}
	}
}

var re = regexp.MustCompile("(_|^)([a-zA-Z])")

func toVimHlGroup(s string) string {
	return strings.ReplaceAll(re.ReplaceAllStringFunc(s, strings.ToUpper), "_", "")
}
