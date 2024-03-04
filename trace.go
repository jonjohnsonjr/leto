// Copyright The OpenTelemetry Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package leto

import (
	"bytes"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"strings"

	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/trace"
)

const (
	// FlagsSampled is a bitmask with the sampled bit set. A SpanContext
	// with the sampling bit set means the span is sampled.
	FlagsSampled = TraceFlags(0x01)

	errInvalidHexID errorConst = "trace-id and span-id can only contain [0-9a-f] characters, all lowercase"

	errInvalidTraceIDLength errorConst = "hex encoded trace-id must have length equals to 32"
	errNilTraceID           errorConst = "trace-id can't be all zero"

	errInvalidSpanIDLength errorConst = "hex encoded span-id must have length equals to 16"
	errNilSpanID           errorConst = "span-id can't be all zero"
)

type errorConst string

func (e errorConst) Error() string {
	return string(e)
}

// TraceID is a unique identity of a trace.
// nolint:revive // revive complains about stutter of `trace.TraceID`.
type TraceID [16]byte

var (
	nilTraceID TraceID
	_          json.Marshaler = nilTraceID
)

// IsValid checks whether the trace TraceID is valid. A valid trace ID does
// not consist of zeros only.
func (t TraceID) IsValid() bool {
	return !bytes.Equal(t[:], nilTraceID[:])
}

// MarshalJSON implements a custom marshal function to encode TraceID
// as a hex string.
func (t TraceID) MarshalJSON() ([]byte, error) {
	return json.Marshal(t.String())
}

func (t *TraceID) UnmarshalJSON(p []byte) error {
	if len(p) <= 2 {
		return nil
	}

	// TODO: strconv.Unquote or something like it?
	p = p[1 : len(p)-1]

	dst := make([]byte, 16)
	n, err := hex.Decode(dst, p)
	if err != nil {
		return err
	}

	if n != 16 {
		return fmt.Errorf("decoding TraceID: saw %d bytes", n)
	}

	// TODO: Just copy?
	*t = [16]byte(dst)

	return nil
}

// String returns the hex string representation form of a TraceID.
func (t TraceID) String() string {
	return hex.EncodeToString(t[:])
}

// SpanID is a unique identity of a span in a trace.
type SpanID [8]byte

var (
	nilSpanID SpanID
	_         json.Marshaler = nilSpanID
)

// IsValid checks whether the SpanID is valid. A valid SpanID does not consist
// of zeros only.
func (s SpanID) IsValid() bool {
	return !bytes.Equal(s[:], nilSpanID[:])
}

// MarshalJSON implements a custom marshal function to encode SpanID
// as a hex string.
func (s SpanID) MarshalJSON() ([]byte, error) {
	return json.Marshal(s.String())
}

func (s *SpanID) UnmarshalJSON(p []byte) error {
	dst := make([]byte, 8)
	if len(p) <= 2 {
		*s = [8]byte(dst)
		return nil
	}
	// TODO: strconv.Unquote or something like it?
	p = p[1 : len(p)-1]
	n, err := hex.Decode(dst, p)
	if err != nil {
		return err
	}

	if n != 8 {
		return fmt.Errorf("decoding SpanID: saw %d bytes", n)
	}

	// TODO: Just copy?
	*s = [8]byte(dst)

	return nil
}

// String returns the hex string representation form of a SpanID.
func (s SpanID) String() string {
	return hex.EncodeToString(s[:])
}

// TraceIDFromHex returns a TraceID from a hex string if it is compliant with
// the W3C trace-context specification.  See more at
// https://www.w3.org/TR/trace-context/#trace-id
// nolint:revive // revive complains about stutter of `trace.TraceIDFromHex`.
func TraceIDFromHex(h string) (TraceID, error) {
	t := TraceID{}
	if len(h) != 32 {
		return t, errInvalidTraceIDLength
	}

	if err := decodeHex(h, t[:]); err != nil {
		return t, err
	}

	if !t.IsValid() {
		return t, errNilTraceID
	}
	return t, nil
}

// SpanIDFromHex returns a SpanID from a hex string if it is compliant
// with the w3c trace-context specification.
// See more at https://www.w3.org/TR/trace-context/#parent-id
func SpanIDFromHex(h string) (SpanID, error) {
	s := SpanID{}
	if len(h) != 16 {
		return s, errInvalidSpanIDLength
	}

	if err := decodeHex(h, s[:]); err != nil {
		return s, err
	}

	if !s.IsValid() {
		return s, errNilSpanID
	}
	return s, nil
}

func decodeHex(h string, b []byte) error {
	for _, r := range h {
		switch {
		case 'a' <= r && r <= 'f':
			continue
		case '0' <= r && r <= '9':
			continue
		default:
			return errInvalidHexID
		}
	}

	decoded, err := hex.DecodeString(h)
	if err != nil {
		return err
	}

	copy(b, decoded)
	return nil
}

// TraceFlags contains flags that can be set on a SpanContext.
type TraceFlags byte //nolint:revive // revive complains about stutter of `trace.TraceFlags`.

// IsSampled returns if the sampling bit is set in the TraceFlags.
func (tf TraceFlags) IsSampled() bool {
	return tf&FlagsSampled == FlagsSampled
}

// WithSampled sets the sampling bit in a new copy of the TraceFlags.
func (tf TraceFlags) WithSampled(sampled bool) TraceFlags { // nolint:revive  // sampled is not a control flag.
	if sampled {
		return tf | FlagsSampled
	}

	return tf &^ FlagsSampled
}

// MarshalJSON implements a custom marshal function to encode TraceFlags
// as a hex string.
func (tf TraceFlags) MarshalJSON() ([]byte, error) {
	return json.Marshal(tf.String())
}

func (tf *TraceFlags) UnmarshalJSON(p []byte) error {
	if len(p) <= 2 {
		return nil
	}

	// TODO: strconv.Unquote or something like it?
	p = p[1 : len(p)-1]

	dst := make([]byte, 1)
	n, err := hex.Decode(dst, p)
	if err != nil {
		return err
	}

	if n != 1 {
		return fmt.Errorf("decoding TraceID: saw %d bytes", n)
	}

	// TODO: Just copy?
	*tf = TraceFlags(dst[0])

	return nil
}

// String returns the hex string representation form of TraceFlags.
func (tf TraceFlags) String() string {
	return hex.EncodeToString([]byte{byte(tf)}[:])
}

// SpanContextConfig contains mutable fields usable for constructing
// an immutable SpanContext.
type SpanContextConfig struct {
	TraceID    TraceID
	SpanID     SpanID
	TraceFlags TraceFlags
	TraceState TraceState
	Remote     bool
}

// NewSpanContext constructs a SpanContext using values from the provided
// SpanContextConfig.
func NewSpanContext(config SpanContextConfig) SpanContext {
	return SpanContext{
		traceID:    config.TraceID,
		spanID:     config.SpanID,
		traceFlags: config.TraceFlags,
		traceState: config.TraceState,
		remote:     config.Remote,
	}
}

// SpanContext contains identifying trace information about a Span.
type SpanContext struct {
	traceID    TraceID
	spanID     SpanID
	traceFlags TraceFlags
	traceState TraceState
	remote     bool
}

var _ json.Marshaler = SpanContext{}
var _ json.Unmarshaler = &SpanContext{}

// IsValid returns if the SpanContext is valid. A valid span context has a
// valid TraceID and SpanID.
func (sc SpanContext) IsValid() bool {
	return sc.HasTraceID() && sc.HasSpanID()
}

// IsRemote indicates whether the SpanContext represents a remotely-created Span.
func (sc SpanContext) IsRemote() bool {
	return sc.remote
}

// WithRemote returns a copy of sc with the Remote property set to remote.
func (sc SpanContext) WithRemote(remote bool) SpanContext {
	return SpanContext{
		traceID:    sc.traceID,
		spanID:     sc.spanID,
		traceFlags: sc.traceFlags,
		traceState: sc.traceState,
		remote:     remote,
	}
}

// TraceID returns the TraceID from the SpanContext.
func (sc SpanContext) TraceID() TraceID {
	return sc.traceID
}

// HasTraceID checks if the SpanContext has a valid TraceID.
func (sc SpanContext) HasTraceID() bool {
	return sc.traceID.IsValid()
}

// WithTraceID returns a new SpanContext with the TraceID replaced.
func (sc SpanContext) WithTraceID(traceID TraceID) SpanContext {
	return SpanContext{
		traceID:    traceID,
		spanID:     sc.spanID,
		traceFlags: sc.traceFlags,
		traceState: sc.traceState,
		remote:     sc.remote,
	}
}

// SpanID returns the SpanID from the SpanContext.
func (sc SpanContext) SpanID() SpanID {
	return sc.spanID
}

// HasSpanID checks if the SpanContext has a valid SpanID.
func (sc SpanContext) HasSpanID() bool {
	return sc.spanID.IsValid()
}

// WithSpanID returns a new SpanContext with the SpanID replaced.
func (sc SpanContext) WithSpanID(spanID SpanID) SpanContext {
	return SpanContext{
		traceID:    sc.traceID,
		spanID:     spanID,
		traceFlags: sc.traceFlags,
		traceState: sc.traceState,
		remote:     sc.remote,
	}
}

// TraceFlags returns the flags from the SpanContext.
func (sc SpanContext) TraceFlags() TraceFlags {
	return sc.traceFlags
}

// IsSampled returns if the sampling bit is set in the SpanContext's TraceFlags.
func (sc SpanContext) IsSampled() bool {
	return sc.traceFlags.IsSampled()
}

// WithTraceFlags returns a new SpanContext with the TraceFlags replaced.
func (sc SpanContext) WithTraceFlags(flags TraceFlags) SpanContext {
	return SpanContext{
		traceID:    sc.traceID,
		spanID:     sc.spanID,
		traceFlags: flags,
		traceState: sc.traceState,
		remote:     sc.remote,
	}
}

// TraceState returns the TraceState from the SpanContext.
func (sc SpanContext) TraceState() TraceState {
	return sc.traceState
}

// WithTraceState returns a new SpanContext with the TraceState replaced.
func (sc SpanContext) WithTraceState(state TraceState) SpanContext {
	return SpanContext{
		traceID:    sc.traceID,
		spanID:     sc.spanID,
		traceFlags: sc.traceFlags,
		traceState: state,
		remote:     sc.remote,
	}
}

// Equal is a predicate that determines whether two SpanContext values are equal.
func (sc SpanContext) Equal(other SpanContext) bool {
	return sc.traceID == other.traceID &&
		sc.spanID == other.spanID &&
		sc.traceFlags == other.traceFlags &&
		sc.traceState.String() == other.traceState.String() &&
		sc.remote == other.remote
}

// MarshalJSON implements a custom marshal function to encode a SpanContext.
func (sc SpanContext) MarshalJSON() ([]byte, error) {
	return json.Marshal(SpanContextConfig{
		TraceID:    sc.traceID,
		SpanID:     sc.spanID,
		TraceFlags: sc.traceFlags,
		TraceState: sc.traceState,
		Remote:     sc.remote,
	})
}

func (sc *SpanContext) UnmarshalJSON(p []byte) error {
	scc := SpanContextConfig{}
	if err := json.Unmarshal(p, &scc); err != nil {
		return err
	}

	sc.traceID = scc.TraceID
	sc.spanID = scc.SpanID
	sc.traceFlags = scc.TraceFlags
	sc.traceState = scc.TraceState
	sc.remote = scc.Remote

	return nil
}

func (sc SpanContext) ToOtel() trace.SpanContext {
	return trace.NewSpanContext(trace.SpanContextConfig{
		TraceID:    trace.TraceID(sc.traceID),
		SpanID:     trace.SpanID(sc.spanID),
		TraceFlags: trace.TraceFlags(sc.traceFlags),
		TraceState: sc.traceState.ts,
		Remote:     sc.remote,
	})
}

// Link is the relationship between two Spans. The relationship can be within
// the same Trace or across different Traces.
//
// For example, a Link is used in the following situations:
//
//  1. Batch Processing: A batch of operations may contain operations
//     associated with one or more traces/spans. Since there can only be one
//     parent SpanContext, a Link is used to keep reference to the
//     SpanContext of all operations in the batch.
//  2. Public Endpoint: A SpanContext for an in incoming client request on a
//     public endpoint should be considered untrusted. In such a case, a new
//     trace with its own identity and sampling decision needs to be created,
//     but this new trace needs to be related to the original trace in some
//     form. A Link is used to keep reference to the original SpanContext and
//     track the relationship.
type Link struct {
	// SpanContext of the linked Span.
	SpanContext SpanContext

	// Attributes describe the aspects of the link.
	Attributes []attribute.KeyValue
}

// SpanKind is the role a Span plays in a Trace.
type SpanKind int

// As a convenience, these match the proto definition, see
// https://github.com/open-telemetry/opentelemetry-proto/blob/30d237e1ff3ab7aa50e0922b5bebdd93505090af/opentelemetry/proto/trace/v1/trace.proto#L101-L129
//
// The unspecified value is not a valid `SpanKind`. Use `ValidateSpanKind()`
// to coerce a span kind to a valid value.
const (
	// SpanKindUnspecified is an unspecified SpanKind and is not a valid
	// SpanKind. SpanKindUnspecified should be replaced with SpanKindInternal
	// if it is received.
	SpanKindUnspecified SpanKind = 0
	// SpanKindInternal is a SpanKind for a Span that represents an internal
	// operation within an application.
	SpanKindInternal SpanKind = 1
	// SpanKindServer is a SpanKind for a Span that represents the operation
	// of handling a request from a client.
	SpanKindServer SpanKind = 2
	// SpanKindClient is a SpanKind for a Span that represents the operation
	// of client making a request to a server.
	SpanKindClient SpanKind = 3
	// SpanKindProducer is a SpanKind for a Span that represents the operation
	// of a producer sending a message to a message broker. Unlike
	// SpanKindClient and SpanKindServer, there is often no direct
	// relationship between this kind of Span and a SpanKindConsumer kind. A
	// SpanKindProducer Span will end once the message is accepted by the
	// message broker which might not overlap with the processing of that
	// message.
	SpanKindProducer SpanKind = 4
	// SpanKindConsumer is a SpanKind for a Span that represents the operation
	// of a consumer receiving a message from a message broker. Like
	// SpanKindProducer Spans, there is often no direct relationship between
	// this Span and the Span that produced the message.
	SpanKindConsumer SpanKind = 5
)

// ValidateSpanKind returns a valid span kind value.  This will coerce
// invalid values into the default value, SpanKindInternal.
func ValidateSpanKind(spanKind SpanKind) SpanKind {
	switch spanKind {
	case SpanKindInternal,
		SpanKindServer,
		SpanKindClient,
		SpanKindProducer,
		SpanKindConsumer:
		// valid
		return spanKind
	default:
		return SpanKindInternal
	}
}

// String returns the specified name of the SpanKind in lower-case.
func (sk SpanKind) String() string {
	switch sk {
	case SpanKindInternal:
		return "internal"
	case SpanKindServer:
		return "server"
	case SpanKindClient:
		return "client"
	case SpanKindProducer:
		return "producer"
	case SpanKindConsumer:
		return "consumer"
	default:
		return "unspecified"
	}
}

const (
	maxListMembers = 32

	listDelimiters  = ","
	memberDelimiter = "="

	errInvalidKey    errorConst = "invalid tracestate key"
	errInvalidValue  errorConst = "invalid tracestate value"
	errInvalidMember errorConst = "invalid tracestate list-member"
	errMemberNumber  errorConst = "too many list-members in tracestate"
	errDuplicate     errorConst = "duplicate list-member in tracestate"
)

type member struct {
	Key   string
	Value string
}

// according to (chr = %x20 / (nblk-char = %x21-2B / %x2D-3C / %x3E-7E) )
// means (chr = %x20-2B / %x2D-3C / %x3E-7E) .
func checkValueChar(v byte) bool {
	return v >= '\x20' && v <= '\x7e' && v != '\x2c' && v != '\x3d'
}

// according to (nblk-chr = %x21-2B / %x2D-3C / %x3E-7E) .
func checkValueLast(v byte) bool {
	return v >= '\x21' && v <= '\x7e' && v != '\x2c' && v != '\x3d'
}

// based on the W3C Trace Context specification
//
//	value    = (0*255(chr)) nblk-chr
//	nblk-chr = %x21-2B / %x2D-3C / %x3E-7E
//	chr      = %x20 / nblk-chr
//
// see https://www.w3.org/TR/trace-context-1/#value
func checkValue(val string) bool {
	n := len(val)
	if n == 0 || n > 256 {
		return false
	}
	for i := 0; i < n-1; i++ {
		if !checkValueChar(val[i]) {
			return false
		}
	}
	return checkValueLast(val[n-1])
}

func checkKeyRemain(key string) bool {
	// ( lcalpha / DIGIT / "_" / "-"/ "*" / "/" )
	for _, v := range key {
		if isAlphaNum(byte(v)) {
			continue
		}
		switch v {
		case '_', '-', '*', '/':
			continue
		}
		return false
	}
	return true
}

// according to
//
//	simple-key = lcalpha (0*255( lcalpha / DIGIT / "_" / "-"/ "*" / "/" ))
//	system-id = lcalpha (0*13( lcalpha / DIGIT / "_" / "-"/ "*" / "/" ))
//
// param n is remain part length, should be 255 in simple-key or 13 in system-id.
func checkKeyPart(key string, n int) bool {
	if len(key) == 0 {
		return false
	}
	first := key[0] // key's first char
	ret := len(key[1:]) <= n
	ret = ret && first >= 'a' && first <= 'z'
	return ret && checkKeyRemain(key[1:])
}

func isAlphaNum(c byte) bool {
	if c >= 'a' && c <= 'z' {
		return true
	}
	return c >= '0' && c <= '9'
}

// according to
//
//	tenant-id = ( lcalpha / DIGIT ) 0*240( lcalpha / DIGIT / "_" / "-"/ "*" / "/" )
//
// param n is remain part length, should be 240 exactly.
func checkKeyTenant(key string, n int) bool {
	if len(key) == 0 {
		return false
	}
	return isAlphaNum(key[0]) && len(key[1:]) <= n && checkKeyRemain(key[1:])
}

// based on the W3C Trace Context specification
//
//	key = simple-key / multi-tenant-key
//	simple-key = lcalpha (0*255( lcalpha / DIGIT / "_" / "-"/ "*" / "/" ))
//	multi-tenant-key = tenant-id "@" system-id
//	tenant-id = ( lcalpha / DIGIT ) (0*240( lcalpha / DIGIT / "_" / "-"/ "*" / "/" ))
//	system-id = lcalpha (0*13( lcalpha / DIGIT / "_" / "-"/ "*" / "/" ))
//	lcalpha    = %x61-7A ; a-z
//
// see https://www.w3.org/TR/trace-context-1/#tracestate-header.
func checkKey(key string) bool {
	tenant, system, ok := strings.Cut(key, "@")
	if !ok {
		return checkKeyPart(key, 255)
	}
	return checkKeyTenant(tenant, 240) && checkKeyPart(system, 13)
}

func newMember(key, value string) (member, error) {
	if !checkKey(key) {
		return member{}, errInvalidKey
	}
	if !checkValue(value) {
		return member{}, errInvalidValue
	}
	return member{Key: key, Value: value}, nil
}

func parseMember(m string) (member, error) {
	key, val, ok := strings.Cut(m, memberDelimiter)
	if !ok {
		return member{}, fmt.Errorf("%w: %s", errInvalidMember, m)
	}
	key = strings.TrimLeft(key, " \t")
	val = strings.TrimRight(val, " \t")
	result, e := newMember(key, val)
	if e != nil {
		return member{}, fmt.Errorf("%w: %s", errInvalidMember, m)
	}
	return result, nil
}

// String encodes member into a string compliant with the W3C Trace Context
// specification.
func (m member) String() string {
	return m.Key + "=" + m.Value
}

// TraceState provides additional vendor-specific trace identification
// information across different distributed tracing systems. It represents an
// immutable list consisting of key/value pairs, each pair is referred to as a
// list-member.
//
// TraceState conforms to the W3C Trace Context specification
// (https://www.w3.org/TR/trace-context-1). All operations that create or copy
// a TraceState do so by validating all input and will only produce TraceState
// that conform to the specification. Specifically, this means that all
// list-member's key/value pairs are valid, no duplicate list-members exist,
// and the maximum number of list-members (32) is not exceeded.
type TraceState struct { //nolint:revive // revive complains about stutter of `trace.TraceState`
	// list is the members in order.
	list []member

	ts trace.TraceState
}

var _ json.Marshaler = TraceState{}
var _ json.Unmarshaler = &TraceState{}

// ParseTraceState attempts to decode a TraceState from the passed
// string. It returns an error if the input is invalid according to the W3C
// Trace Context specification.
func ParseTraceState(ts string) (TraceState, error) {
	if ts == "" {
		return TraceState{}, nil
	}

	wrapErr := func(err error) error {
		return fmt.Errorf("failed to parse tracestate: %w", err)
	}

	var members []member
	found := make(map[string]struct{})
	for ts != "" {
		var memberStr string
		memberStr, ts, _ = strings.Cut(ts, listDelimiters)
		if len(memberStr) == 0 {
			continue
		}

		m, err := parseMember(memberStr)
		if err != nil {
			return TraceState{}, wrapErr(err)
		}

		if _, ok := found[m.Key]; ok {
			return TraceState{}, wrapErr(errDuplicate)
		}
		found[m.Key] = struct{}{}

		members = append(members, m)
		if n := len(members); n > maxListMembers {
			return TraceState{}, wrapErr(errMemberNumber)
		}
	}

	return TraceState{list: members}, nil
}

// MarshalJSON marshals the TraceState into JSON.
func (ts TraceState) MarshalJSON() ([]byte, error) {
	return json.Marshal(ts.String())
}

func (ts *TraceState) UnmarshalJSON(p []byte) error {
	if len(p) <= 2 {
		return nil
	}

	p = p[1 : len(p)-1]

	tts, err := trace.ParseTraceState(string(p))
	if err != nil {
		return err
	}

	ts.ts = tts

	return nil
}

// String encodes the TraceState into a string compliant with the W3C
// Trace Context specification. The returned string will be invalid if the
// TraceState contains any invalid members.
func (ts TraceState) String() string {
	if len(ts.list) == 0 {
		return ""
	}
	var n int
	n += len(ts.list)     // member delimiters: '='
	n += len(ts.list) - 1 // list delimiters: ','
	for _, mem := range ts.list {
		n += len(mem.Key)
		n += len(mem.Value)
	}

	var sb strings.Builder
	sb.Grow(n)
	_, _ = sb.WriteString(ts.list[0].Key)
	_ = sb.WriteByte('=')
	_, _ = sb.WriteString(ts.list[0].Value)
	for i := 1; i < len(ts.list); i++ {
		_ = sb.WriteByte(listDelimiters[0])
		_, _ = sb.WriteString(ts.list[i].Key)
		_ = sb.WriteByte('=')
		_, _ = sb.WriteString(ts.list[i].Value)
	}
	return sb.String()
}

// Get returns the value paired with key from the corresponding TraceState
// list-member if it exists, otherwise an empty string is returned.
func (ts TraceState) Get(key string) string {
	for _, member := range ts.list {
		if member.Key == key {
			return member.Value
		}
	}

	return ""
}

// Insert adds a new list-member defined by the key/value pair to the
// TraceState. If a list-member already exists for the given key, that
// list-member's value is updated. The new or updated list-member is always
// moved to the beginning of the TraceState as specified by the W3C Trace
// Context specification.
//
// If key or value are invalid according to the W3C Trace Context
// specification an error is returned with the original TraceState.
//
// If adding a new list-member means the TraceState would have more members
// then is allowed, the new list-member will be inserted and the right-most
// list-member will be dropped in the returned TraceState.
func (ts TraceState) Insert(key, value string) (TraceState, error) {
	m, err := newMember(key, value)
	if err != nil {
		return ts, err
	}
	n := len(ts.list)
	found := n
	for i := range ts.list {
		if ts.list[i].Key == key {
			found = i
		}
	}
	cTS := TraceState{}
	if found == n && n < maxListMembers {
		cTS.list = make([]member, n+1)
	} else {
		cTS.list = make([]member, n)
	}
	cTS.list[0] = m
	// When the number of members exceeds capacity, drop the "right-most".
	copy(cTS.list[1:], ts.list[0:found])
	if found < n {
		copy(cTS.list[1+found:], ts.list[found+1:])
	}
	return cTS, nil
}

// Delete returns a copy of the TraceState with the list-member identified by
// key removed.
func (ts TraceState) Delete(key string) TraceState {
	members := make([]member, ts.Len())
	copy(members, ts.list)
	for i, member := range ts.list {
		if member.Key == key {
			members = append(members[:i], members[i+1:]...)
			// TraceState should contain no duplicate members.
			break
		}
	}
	return TraceState{list: members}
}

// Len returns the number of list-members in the TraceState.
func (ts TraceState) Len() int {
	return len(ts.list)
}
