package core

import (
	"bytes"
	"context"
	"crypto/aes"
	"crypto/cipher"
	"crypto/md5"
	"crypto/rand"
	"crypto/sha256"
	"crypto/subtle"
	"crypto/tls"
	"encoding/base64"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	mrand "math/rand"
	"net/http"
	"net/url"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"sync"
	"time"

	"golang.org/x/net/html"
)

const (
	// yeguoBaseURL 为兜底线路：中转站随机线路全部不可用时才使用。
	yeguoBaseURL = "https://yeguodj.com"
	// yeguoAPIBaseDefault 是新版野果页面写死在 JS 里的接口入口（路由仍以 /api/ 开头）。
	yeguoAPIBaseDefault = "https://ygdj17.com/api.php"
	yeguoTransitURL     = "https://ygdj7.com"
)

// yeguoLineCacheTTL 控制中转站随机线路的缓存时间。
const yeguoLineCacheTTL = 10 * time.Minute

var (
	errYeguoDecode        = errors.New("野果接口响应校验或解码失败")
	yeguoModuleImport     = regexp.MustCompile(`(?s)import\s*\{([^{};]+)\}\s*from\s*["'\x60]([^"'\x60]+)["'\x60]`)
	yeguoPublicField      = regexp.MustCompile(`\b(version|mode|padding|key|iv|sign_key)\s*:\s*(?:[a-zA-Z_$][a-zA-Z0-9_$]*\(\s*)?["'\x60]([^"'\x60\\\r\n]{1,512})["'\x60]`)
	yeguoTransitBase64    = regexp.MustCompile(`Base64\.decode\(["']([A-Za-z0-9+/=]{128,})["']\)`)
	yeguoTransitSuffix    = regexp.MustCompile(`(?i)\+\s*["']\.([a-z0-9-]+(?:\.[a-z0-9-]+)+)["']`)
	yeguoTransitWords     = regexp.MustCompile(`(?s)\bwords\s*=\s*["']([^"']+)["']\s*\.split\(["'],["']\)`)
	yeguoTransitLiteral   = regexp.MustCompile(`https?://[a-z0-9-]+(?:\.[a-z0-9-]+)+/?`)
	yeguoTransitHostLabel = regexp.MustCompile(`^[a-z0-9][a-z0-9-]{0,62}$`)
)

type yeguoAccess struct {
	base       string
	site       string
	key        []byte
	iv         []byte
	signKey    []byte
	identifier string
	loadedAt   time.Time
}

type yeguoAccessCall struct {
	done   chan struct{}
	access *yeguoAccess
	err    error
}

type yeguoAPIClient struct {
	downloader *Downloader
	site       string
	mu         sync.Mutex
	access     *yeguoAccess
	pending    *yeguoAccessCall
	httpOnce   sync.Once
	httpClient *http.Client

	linesMu sync.Mutex
	lines   []string
	linesAt time.Time
}

func (d *Downloader) yeguoClient() *yeguoAPIClient {
	d.yeguoOnce.Do(func() {
		d.yeguo = &yeguoAPIClient{downloader: d, site: d.providerBaseURL(sourceYeguo)}
	})
	return d.yeguo
}

func (client *yeguoAPIClient) siteURL() string {
	client.mu.Lock()
	defer client.mu.Unlock()
	if client.access != nil && client.access.site != "" {
		return client.access.site
	}
	if client.site != "" {
		return client.site
	}
	return yeguoBaseURL
}

func validYeguoSite(raw string) string {
	address, err := url.Parse(strings.TrimSpace(raw))
	if err != nil || !isProviderHTTPMediaURL(raw) || address.User != nil || address.RawQuery != "" || address.Fragment != "" || address.Host == "" {
		return ""
	}
	source := providerSourceForURL(address.String())
	if source != sourceYeguo {
		return ""
	}
	address.Path = strings.TrimRight(address.EscapedPath(), "/")
	if address.Path != "" {
		return ""
	}
	return strings.TrimRight(address.String(), "/")
}

func isYeguoActiveSite(raw string) bool {
	address, err := url.Parse(raw)
	if err != nil {
		return false
	}
	host := strings.ToLower(address.Hostname())
	switch host {
	case "yeguodj.com", "www.yeguodj.com", "ygdj17.com", "www.ygdj17.com", "ygdj7.com", "www.ygdj7.com":
		return true
	}
	return isYeguoLineHost(host)
}

// yeguoLineSuffixes 是中转站随机线路的初始后缀。
// 后缀会轮换（实测见过 gfqbmosa.cc / cyqpdsqc.cc / fzchosdi.cc），
// 每次解析中转站页面后由 yeguoRegisterSuffixes 动态补充，不能写死。
var yeguoLineSuffixes = []string{"gfqbmosa.cc", "cyqpdsqc.cc", "fzchosdi.cc", "buxefaex.cc"}

var (
	yeguoSuffixMu sync.RWMutex
	yeguoSuffixes = map[string]bool{
		"gfqbmosa.cc": true,
		"cyqpdsqc.cc": true,
		"fzchosdi.cc": true,
		"buxefaex.cc": true,
	}
)

// yeguoRegisterSuffixes 记录中转站当前使用的线路后缀，避免后缀轮换后线路被过滤掉。
func yeguoRegisterSuffixes(suffixes []string) {
	if len(suffixes) == 0 {
		return
	}
	yeguoSuffixMu.Lock()
	defer yeguoSuffixMu.Unlock()
	for _, suffix := range suffixes {
		suffix = strings.ToLower(strings.Trim(strings.TrimSpace(suffix), "."))
		if suffix == "" || !strings.Contains(suffix, ".") {
			continue
		}
		yeguoSuffixes[suffix] = true
	}
}

// isYeguoLineHost 判断主机名是否属于野果随机线路（含动态发现的轮换后缀）。
func isYeguoLineHost(host string) bool {
	host = strings.ToLower(strings.TrimSpace(host))
	if host == "" {
		return false
	}
	yeguoSuffixMu.RLock()
	defer yeguoSuffixMu.RUnlock()
	if yeguoSuffixes[host] {
		return true
	}
	for suffix := range yeguoSuffixes {
		if strings.HasSuffix(host, "."+suffix) {
			return true
		}
	}
	return false
}

func yeguoTransitDecodedText(body string) string {
	var parts []string
	parts = append(parts, body)
	for _, match := range yeguoTransitBase64.FindAllStringSubmatch(body, 4) {
		decoded, err := base64.StdEncoding.DecodeString(match[1])
		if err == nil {
			parts = append(parts, string(decoded))
		}
	}
	return strings.Join(parts, "\n")
}

// yeguoTransitWordsList 返回中转站页面词表（浏览器用 words.random() 随机取词）。
func yeguoTransitWordsList(text string) []string {
	match := yeguoTransitWords.FindStringSubmatch(text)
	if len(match) < 2 || len(match[1]) > 200000 {
		return nil
	}
	var words []string
	seen := map[string]bool{}
	for _, word := range strings.Split(match[1], ",") {
		word = strings.ToLower(strings.TrimSpace(word))
		if yeguoTransitHostLabel.MatchString(word) && !seen[word] {
			seen[word] = true
			words = append(words, word)
		}
	}
	return words
}

// yeguoTransitSuffixList 返回页面里出现的线路后缀，保持出现顺序（首选在前）。
func yeguoTransitSuffixList(text string) []string {
	var suffixes []string
	seen := map[string]bool{}
	for _, match := range yeguoTransitSuffix.FindAllStringSubmatch(text, 16) {
		suffix := strings.ToLower(strings.Trim(strings.TrimSpace(match[1]), "."))
		if suffix == "" || !strings.Contains(suffix, ".") || seen[suffix] {
			continue
		}
		seen[suffix] = true
		suffixes = append(suffixes, suffix)
	}
	yeguoRegisterSuffixes(suffixes)
	return suffixes
}

// yeguoTransitSites 复现中转站的生成规则：词表随机词 + 后缀，按后缀优先顺序枚举候选。
func yeguoTransitSites(body string) []string {
	text := yeguoTransitDecodedText(body)
	words := yeguoTransitWordsList(text)
	suffixes := yeguoTransitSuffixList(text)
	if len(suffixes) == 0 {
		suffixes = append([]string(nil), yeguoLineSuffixes...)
	}
	if len(words) == 0 {
		words = []string{"analyze", "ability", "abandon"}
	}
	var sites []string
	seen := map[string]bool{}
	add := func(site string) {
		if site = validYeguoSite(site); site != "" && site != yeguoTransitURL && !seen[site] {
			seen[site] = true
			sites = append(sites, site)
		}
	}
	for _, match := range yeguoTransitLiteral.FindAllString(text, 32) {
		host := strings.ToLower(match)
		if isYeguoActiveSite(host) && !strings.Contains(host, "yeguodj.com") {
			add(match)
		}
	}
	for _, suffix := range suffixes {
		for _, word := range words {
			add("https://" + word + "." + suffix)
		}
	}
	return sites
}

// yeguoRandomLineCandidates 按 words.random() 的规则抽样，每个后缀取 perSuffix 个随机词。
func yeguoRandomLineCandidates(text string, perSuffix int) []string {
	words := yeguoTransitWordsList(text)
	suffixes := yeguoTransitSuffixList(text)
	if len(suffixes) == 0 {
		suffixes = append([]string(nil), yeguoLineSuffixes...)
	}
	if len(words) == 0 || perSuffix <= 0 {
		return nil
	}
	rng := mrand.New(mrand.NewSource(time.Now().UnixNano()))
	var sites []string
	seen := map[string]bool{}
	for _, suffix := range suffixes {
		for i := 0; i < perSuffix; i++ {
			for attempt := 0; attempt < 8; attempt++ {
				word := words[rng.Intn(len(words))]
				site := "https://" + word + "." + suffix
				if seen[site] {
					continue
				}
				seen[site] = true
				sites = append(sites, site)
				break
			}
		}
	}
	return sites
}

// yeguoLineUsable 判断一条随机线路是否真的返回野果页面（不是泛解析的空白页）。
func (client *yeguoAPIClient) yeguoLineUsable(ctx context.Context, site string) bool {
	request, err := http.NewRequestWithContext(ctx, http.MethodGet, site+"/", nil)
	if err != nil {
		return false
	}
	request.Header.Set("User-Agent", userAgent)
	response, err := client.do(ctx, request, 8*time.Second)
	if err != nil {
		return false
	}
	body, readErr := io.ReadAll(io.LimitReader(response.Body, 512<<10))
	response.Body.Close()
	if readErr != nil || response.StatusCode < 200 || response.StatusCode >= 300 {
		return false
	}
	text := string(body)
	return strings.Contains(text, "__NUXT_DATA__") && strings.Contains(text, "_nuxt/")
}

// transitLines 抓中转站页面，按它的随机规则抽样并并发探活，结果缓存 10 分钟。
func (client *yeguoAPIClient) transitLines(ctx context.Context) []string {
	client.linesMu.Lock()
	if len(client.lines) > 0 {
		if age := time.Since(client.linesAt); age >= 0 && age < yeguoLineCacheTTL {
			lines := append([]string(nil), client.lines...)
			client.linesMu.Unlock()
			return lines
		}
	}
	client.linesMu.Unlock()

	body, err := client.downloader.fetchProviderText(context.WithValue(ctx, providerTextNoCacheKey{}, true), yeguoTransitURL+"/", yeguoTransitURL+"/")
	if err != nil {
		return nil
	}
	candidates := yeguoRandomLineCandidates(yeguoTransitDecodedText(body), 4)
	if len(candidates) == 0 {
		return nil
	}
	probeCtx, cancel := context.WithTimeout(ctx, 20*time.Second)
	defer cancel()
	type probeResult struct {
		index int
		site  string
	}
	results := make(chan probeResult, len(candidates))
	sem := make(chan struct{}, 6)
	var wg sync.WaitGroup
	for index, site := range candidates {
		wg.Add(1)
		go func(index int, site string) {
			defer wg.Done()
			select {
			case sem <- struct{}{}:
			case <-probeCtx.Done():
				return
			}
			defer func() { <-sem }()
			if client.yeguoLineUsable(probeCtx, site) {
				results <- probeResult{index: index, site: site}
			}
		}(index, site)
	}
	go func() { wg.Wait(); close(results) }()
	var found []probeResult
	for item := range results {
		found = append(found, item)
	}
	sort.Slice(found, func(i, j int) bool { return found[i].index < found[j].index })
	var lines []string
	for _, item := range found {
		lines = append(lines, item.site)
	}
	client.linesMu.Lock()
	client.lines, client.linesAt = lines, time.Now()
	client.linesMu.Unlock()
	return lines
}

func (client *yeguoAPIClient) discoverTransitSites(ctx context.Context) []string {
	return client.transitLines(ctx)
}

func (client *yeguoAPIClient) configuration(ctx context.Context) (*yeguoAccess, error) {
	if err := ctx.Err(); err != nil {
		return nil, err
	}
	client.mu.Lock()
	if access := client.access; access != nil && time.Since(access.loadedAt) >= 0 && time.Since(access.loadedAt) < time.Hour {
		client.mu.Unlock()
		return access, nil
	}
	if pending := client.pending; pending != nil {
		client.mu.Unlock()
		select {
		case <-pending.done:
			if (errors.Is(pending.err, context.Canceled) || errors.Is(pending.err, context.DeadlineExceeded)) && ctx.Err() == nil {
				return client.configuration(ctx)
			}
			return pending.access, pending.err
		case <-ctx.Done():
			return nil, ctx.Err()
		}
	}
	pending := &yeguoAccessCall{done: make(chan struct{})}
	client.pending = pending
	client.mu.Unlock()

	access, err := client.discoverConfiguration(ctx)
	client.mu.Lock()
	if err == nil {
		client.access = access
	}
	pending.access, pending.err = access, err
	client.pending = nil
	close(pending.done)
	client.mu.Unlock()
	return access, err
}

func (client *yeguoAPIClient) requestClient() *http.Client {
	client.httpOnce.Do(func() {
		if client.downloader.client != nil && client.downloader.client.Transport != nil {
			if _, production := client.downloader.client.Transport.(*huangguoBrowserTransport); !production {
				client.httpClient = &http.Client{Transport: client.downloader.client.Transport}
				return
			}
		}
		transport := http.DefaultTransport.(*http.Transport).Clone()
		transport.TLSClientConfig = &tls.Config{MinVersion: tls.VersionTLS12}
		if client.downloader.cfg.InsecureTLS {
			transport.TLSClientConfig = transport.TLSClientConfig.Clone()
			transport.TLSClientConfig.InsecureSkipVerify = true
		}
		if client.downloader.proxyRouter != nil {
			transport.Proxy = client.downloader.proxyRouter.proxy
		}
		client.httpClient = &http.Client{
			Transport: transport,
			CheckRedirect: func(request *http.Request, via []*http.Request) error {
				if len(via) >= 10 {
					return errors.New("野果接口重定向次数过多")
				}
				return nil
			},
		}
	})
	return client.httpClient
}

func (client *yeguoAPIClient) do(ctx context.Context, request *http.Request, timeout time.Duration) (*http.Response, error) {
	release := func() {}
	var err error
	if client.downloader.limiter != nil {
		release, err = client.downloader.limiter.acquire(ctx, request)
		if err != nil {
			return nil, err
		}
	}
	cancel := func() {}
	if timeout > 0 {
		ctx, cancel = context.WithTimeout(ctx, timeout)
		request = request.WithContext(ctx)
	}
	response, err := client.requestClient().Do(request)
	if err != nil {
		cancel()
		release()
		return nil, err
	}
	if client.downloader.limiter != nil {
		client.downloader.limiter.observe(request, response)
	}
	observeSourceResponse(ctx, response)
	response.Body = &limitedResponseBody{ReadCloser: response.Body, release: func() { cancel(); release() }}
	return response, nil
}

func yeguoAPIBase(document *html.Node, configured, site string) (string, error) {
	base := strings.TrimRight(configured, "/")
	if base == "" {
		for _, node := range providerHTMLNodes(document, func(node *html.Node) bool {
			return node.Data == "script" && providerHTMLAttr(node, "id") == "__NUXT_DATA__"
		}) {
			if node.FirstChild == nil {
				continue
			}
			var table []json.RawMessage
			if json.Unmarshal([]byte(node.FirstChild.Data), &table) != nil || len(table) > 100000 {
				continue
			}
			for _, raw := range table {
				var fields map[string]json.RawMessage
				if json.Unmarshal(raw, &fields) != nil || fields["apiBaseURL"] == nil {
					continue
				}
				var reference int
				if json.Unmarshal(fields["apiBaseURL"], &reference) == nil && reference >= 0 && reference < len(table) {
					_ = json.Unmarshal(table[reference], &base)
				}
				if base != "" {
					break
				}
			}
		}
	}
	if base == "" {
		// 新版野果页面不再提供 apiBaseURL，但每条随机线路自带 /api.php，
		// 实测 1~2 秒返回，远快于写死的兜底入口（后者要 25 秒）。
		if candidate := strings.TrimRight(site, "/") + "/api.php"; isProviderHTTPMediaURL(candidate) {
			base = candidate
		}
	}
	if base == "" {
		base = yeguoAPIBaseDefault
	}
	address, err := url.Parse(base)
	if err != nil || !isProviderHTTPMediaURL(base) || address.User != nil || address.RawQuery != "" || address.Fragment != "" {
		return "", errors.New("野果页面未提供有效的接口入口")
	}
	return strings.TrimRight(base, "/"), nil
}

func yeguoScriptURL(base, reference string) string {
	page, err := url.Parse(base)
	if err != nil {
		return ""
	}
	address, err := url.Parse(reference)
	if err != nil {
		return ""
	}
	address = page.ResolveReference(address)
	if address.User != nil || providerMediaOrigin(address) != providerMediaOrigin(page) ||
		!strings.HasPrefix(address.Path, "/_nuxt/") || !strings.HasSuffix(address.Path, ".js") {
		return ""
	}
	address.Fragment = ""
	return address.String()
}

func yeguoPublicBytes(value string) []byte {
	if !strings.Contains(value, "_") {
		return []byte(value)
	}
	var decoded []byte
	for _, part := range strings.Split(value, "_") {
		number, err := strconv.ParseUint(part, 10, 8)
		if err != nil {
			return nil
		}
		decoded = append(decoded, byte(number))
	}
	return decoded
}

func parseYeguoPublicConfiguration(script string) *yeguoAccess {
	fields := map[string]string{}
	for _, match := range yeguoPublicField.FindAllStringSubmatch(script, 32) {
		fields[match[1]] = match[2]
	}
	if fields["version"] != "v0" || fields["mode"] != "CBC" || fields["padding"] != "Pkcs7" {
		return nil
	}
	access := &yeguoAccess{key: yeguoPublicBytes(fields["key"]), iv: yeguoPublicBytes(fields["iv"]),
		signKey: yeguoPublicBytes(fields["sign_key"])}
	if (len(access.key) != 16 && len(access.key) != 24 && len(access.key) != 32) ||
		len(access.iv) != aes.BlockSize || len(access.signKey) == 0 || len(access.signKey) > 128 {
		return nil
	}
	return access
}

func (client *yeguoAPIClient) discoverConfiguration(ctx context.Context) (*yeguoAccess, error) {
	ctx, cancel := context.WithTimeout(ctx, 30*time.Second)
	defer cancel()
	seen := map[string]bool{}
	var sites []string
	add := func(site string) {
		if site = validYeguoSite(site); site != "" && isYeguoActiveSite(site) && !seen[site] {
			seen[site] = true
			sites = append(sites, site)
		}
	}
	// 首选：从中转站随机生成并探活通过的线路。
	for _, site := range client.discoverTransitSites(ctx) {
		add(site)
	}
	add(client.site)
	// 兜底：yeguodj.com 永远排最后。
	add(yeguoBaseURL)
	var lastErr error
	for _, site := range sites {
		access, err := client.discoverConfigurationAt(ctx, site)
		if err == nil {
			return access, nil
		}
		lastErr = err
	}
	return nil, errors.Join(errors.New("野果线路暂不可用，请稍后重试"), lastErr)
}

func (client *yeguoAPIClient) discoverConfigurationAt(ctx context.Context, site string) (*yeguoAccess, error) {
	d := client.downloader
	document, pageURL, err := d.fetchProviderPage(ctx, site+"/", site+"/", "")
	if err != nil {
		return nil, err
	}
	apiBase, err := yeguoAPIBase(document, d.cfg.YeguoAPIURL, site)
	if err != nil {
		return nil, err
	}
	entry := ""
	for _, script := range providerHTMLNodes(document, func(node *html.Node) bool {
		return node.Data == "script" && providerHTMLAttr(node, "type") == "module"
	}) {
		if entry = yeguoScriptURL(pageURL, providerHTMLAttr(script, "src")); entry != "" {
			break
		}
	}
	if entry == "" {
		return nil, errors.New("野果页面未提供接口配置脚本")
	}
	entryBody, err := d.fetchProviderText(ctx, entry, pageURL)
	if err != nil {
		return nil, err
	}
	imports := yeguoModuleImport.FindAllStringSubmatch(entryBody, 64)
	sort.SliceStable(imports, func(i, j int) bool {
		return !strings.Contains(imports[i][1], ",") && strings.Contains(imports[j][1], ",")
	})
	seen := map[string]bool{}
	var lastErr error
	for _, imported := range imports {
		if len(imported[1]) > 2400 {
			continue
		}
		address := yeguoScriptURL(entry, imported[2])
		if address == "" || seen[address] {
			continue
		}
		if len(seen) >= 20 {
			break
		}
		seen[address] = true
		body, err := d.fetchProviderText(ctx, address, pageURL)
		if err != nil {
			lastErr = err
			var backoff *requestBackoff
			if errors.As(err, &backoff) || ctx.Err() != nil {
				return nil, err
			}
			continue
		}
		access := parseYeguoPublicConfiguration(body)
		if access == nil {
			continue
		}
		var identifier [16]byte
		if _, err := rand.Read(identifier[:]); err != nil {
			return nil, errors.New("无法初始化野果请求会话")
		}
		access.base, access.site, access.identifier, access.loadedAt = apiBase, site, hex.EncodeToString(identifier[:]), time.Now()
		return access, nil
	}
	return nil, errors.Join(errors.New("野果接口配置已变化，暂时无法解码，请稍后重试"), lastErr)
}

func decodeYeguoJSONObject(body []byte) (map[string]any, error) {
	decoder := json.NewDecoder(bytes.NewReader(body))
	decoder.UseNumber()
	var value map[string]any
	if decoder.Decode(&value) != nil || value == nil || decoder.Decode(new(any)) != io.EOF {
		return nil, errYeguoDecode
	}
	return value, nil
}

func yeguoResponseSignature(value map[string]any, key []byte) (string, error) {
	var fields []string
	for name, field := range value {
		if name != "sign" && name != "_ver" && field != nil {
			fields = append(fields, name)
		}
	}
	sort.Strings(fields)
	var pieces []string
	for _, name := range fields {
		var field string
		switch value := value[name].(type) {
		case string:
			field = value
		case json.Number:
			field = value.String()
		case bool:
			field = strconv.FormatBool(value)
		default:
			return "", errYeguoDecode
		}
		if name == "data" {
			field = strings.ReplaceAll(field, " ", "+")
		}
		pieces = append(pieces, name+"="+field)
	}
	digest := sha256.Sum256(append([]byte(strings.Join(pieces, "&")), key...))
	signature := md5.Sum([]byte(hex.EncodeToString(digest[:])))
	return hex.EncodeToString(signature[:]), nil
}

func decodeYeguoResponse(body []byte, access *yeguoAccess) (map[string]any, error) {
	envelope, err := decodeYeguoJSONObject(body)
	if err != nil {
		return nil, err
	}
	if signature := mapString(envelope, "sign"); signature != "" {
		expected, err := yeguoResponseSignature(envelope, access.signKey)
		if err != nil || subtle.ConstantTimeCompare([]byte(expected), []byte(strings.ToLower(signature))) != 1 {
			return nil, errYeguoDecode
		}
	}
	if encoded, encrypted := envelope["data"].(string); encrypted {
		if access == nil || len(access.iv) != aes.BlockSize {
			return nil, errYeguoDecode
		}
		ciphertext, err := base64.StdEncoding.DecodeString(strings.ReplaceAll(strings.TrimSpace(encoded), " ", "+"))
		if err != nil || len(ciphertext) == 0 || len(ciphertext)%aes.BlockSize != 0 {
			return nil, errYeguoDecode
		}
		block, err := aes.NewCipher(access.key)
		if err != nil {
			return nil, errYeguoDecode
		}
		plain := make([]byte, len(ciphertext))
		cipher.NewCBCDecrypter(block, access.iv).CryptBlocks(plain, ciphertext)
		plain, err = pkcs7Unpad(plain, aes.BlockSize)
		if err != nil {
			return nil, errYeguoDecode
		}
		return decodeYeguoJSONObject(plain)
	}
	return envelope, nil
}

func (client *yeguoAPIClient) call(ctx context.Context, route string, parameters url.Values) (map[string]any, error) {
	for attempt := 0; attempt < 2; attempt++ {
		access, err := client.configuration(ctx)
		if err != nil {
			return nil, err
		}
		values := url.Values{"bundleId": {"com.pwa.mater"}, "version": {"1.3.2"}, "oauth_type": {"web"},
			"language": {"zh"}, "via": {"pwa"}, "oauth_id": {access.identifier}, "trace_id": {access.identifier}, "token": {""}}
		for key, value := range parameters {
			values[key] = append([]string(nil), value...)
		}
		method := http.MethodPost
		if route == "/api/home/contentOptions" {
			method = http.MethodGet
		}
		address := access.base + route
		var requestBody io.Reader
		if method == http.MethodGet {
			address += "?" + values.Encode()
		} else {
			requestBody = strings.NewReader(values.Encode())
		}
		request, err := http.NewRequestWithContext(ctx, method, address, requestBody)
		if err != nil {
			return nil, errors.New("野果接口地址无效")
		}
		request.Header.Set("User-Agent", userAgent)
		if method == http.MethodPost {
			request.Header.Set("Content-Type", "application/x-www-form-urlencoded")
		}
		request.Header.Set("Accept", "application/json, text/plain, */*")
		site := firstNonEmpty(access.site, client.site, yeguoBaseURL)
		request.Header.Set("Origin", site)
		request.Header.Set("Referer", site+"/")
		timeout := 30 * time.Second
		if background, _ := ctx.Value(backgroundCatalogKey{}).(bool); background {
			timeout = 8 * time.Second
		}
		response, err := client.do(ctx, request, timeout)
		if err != nil {
			return nil, err
		}
		body, readErr := io.ReadAll(io.LimitReader(response.Body, (8<<20)+1))
		response.Body.Close()
		if response.StatusCode < 200 || response.StatusCode >= 300 || catalogResponseBlockReason(response, body) != "" {
			return nil, client.downloader.catalogResponseError(request, response, body)
		}
		if readErr != nil || len(body) > 8<<20 {
			return nil, errors.New("野果接口数据过大或读取失败")
		}
		payload, err := decodeYeguoResponse(body, access)
		if errors.Is(err, errYeguoDecode) && attempt == 0 {
			client.mu.Lock()
			if client.access == access {
				client.access = nil
			}
			client.mu.Unlock()
			continue
		}
		if err != nil {
			return nil, err
		}
		if mapString(payload, "status") != "1" {
			if mapString(payload, "status") == "-1" {
				return nil, errors.New("野果当前内容需要站源授权")
			}
			return nil, fmt.Errorf("野果请求未完成：%s", firstNonEmpty(truncate(cleanText(mapString(payload, "msg")), 180), "请稍后重试"))
		}
		data, valid := payload["data"].(map[string]any)
		if !valid {
			return nil, errors.New("野果返回的数据格式无效")
		}
		return data, nil
	}
	return nil, errYeguoDecode
}
