// Copyright The OpenTelemetry Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
package leto

import (
	"time"

	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/sdk/instrumentation"
	"go.opentelemetry.io/otel/sdk/resource"
	tracesdk "go.opentelemetry.io/otel/sdk/trace"
	"go.opentelemetry.io/otel/trace"
)

func toAttributes(kvs []KeyValue) []attribute.KeyValue {
	out := make([]attribute.KeyValue, 0, len(kvs))
	for _, kv := range kvs {
		out = append(out, kv.Otel())
	}
	return out
}

// From go.opentelemetry.io/otel/sdk/trace/tracetest

// SpanStub is a stand-in for a Span.
type SpanStub struct {
	Name                   string
	SpanContext            SpanContext
	Parent                 SpanContext
	SpanKind               trace.SpanKind
	StartTime              time.Time
	EndTime                time.Time
	Attributes             []KeyValue
	Events                 []tracesdk.Event
	Links                  []tracesdk.Link
	Status                 tracesdk.Status
	DroppedAttributes      int
	DroppedEvents          int
	DroppedLinks           int
	ChildSpanCount         int
	Resource               []KeyValue
	InstrumentationLibrary instrumentation.Library
}

// Snapshot returns a read-only copy of the SpanStub.
func (s SpanStub) Snapshot() tracesdk.ReadOnlySpan {
	return spanSnapshot{
		name:                 s.Name,
		spanContext:          s.SpanContext.ToOtel(),
		parent:               s.Parent.ToOtel(),
		spanKind:             s.SpanKind,
		startTime:            s.StartTime,
		endTime:              s.EndTime,
		attributes:           toAttributes(s.Attributes),
		events:               s.Events,
		links:                s.Links,
		status:               s.Status,
		droppedAttributes:    s.DroppedAttributes,
		droppedEvents:        s.DroppedEvents,
		droppedLinks:         s.DroppedLinks,
		childSpanCount:       s.ChildSpanCount,
		resource:             resource.NewSchemaless(toAttributes(s.Resource)...),
		instrumentationScope: s.InstrumentationLibrary,
	}
}

type spanSnapshot struct {
	// Embed the interface to implement the private method.
	tracesdk.ReadOnlySpan

	name                 string
	spanContext          trace.SpanContext
	parent               trace.SpanContext
	spanKind             trace.SpanKind
	startTime            time.Time
	endTime              time.Time
	attributes           []attribute.KeyValue
	events               []tracesdk.Event
	links                []tracesdk.Link
	status               tracesdk.Status
	droppedAttributes    int
	droppedEvents        int
	droppedLinks         int
	childSpanCount       int
	resource             *resource.Resource
	instrumentationScope instrumentation.Scope
}

func (s spanSnapshot) Name() string                     { return s.name }
func (s spanSnapshot) SpanContext() trace.SpanContext   { return s.spanContext }
func (s spanSnapshot) Parent() trace.SpanContext        { return s.parent }
func (s spanSnapshot) SpanKind() trace.SpanKind         { return s.spanKind }
func (s spanSnapshot) StartTime() time.Time             { return s.startTime }
func (s spanSnapshot) EndTime() time.Time               { return s.endTime }
func (s spanSnapshot) Attributes() []attribute.KeyValue { return s.attributes }
func (s spanSnapshot) Links() []tracesdk.Link           { return s.links }
func (s spanSnapshot) Events() []tracesdk.Event         { return s.events }
func (s spanSnapshot) Status() tracesdk.Status          { return s.status }
func (s spanSnapshot) DroppedAttributes() int           { return s.droppedAttributes }
func (s spanSnapshot) DroppedLinks() int                { return s.droppedLinks }
func (s spanSnapshot) DroppedEvents() int               { return s.droppedEvents }
func (s spanSnapshot) ChildSpanCount() int              { return s.childSpanCount }
func (s spanSnapshot) Resource() *resource.Resource     { return s.resource }
func (s spanSnapshot) InstrumentationScope() instrumentation.Scope {
	return s.instrumentationScope
}

func (s spanSnapshot) InstrumentationLibrary() instrumentation.Library {
	return s.instrumentationScope
}
