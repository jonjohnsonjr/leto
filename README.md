# leto

This is a tiny fork of otel's go sdk to make it possible to unmarshal JSON.

The only thing I care about is being able to parse [stdouttrace](https://pkg.go.dev/go.opentelemetry.io/otel/exporters/stdout/stdouttrace) output.

In an ideal world, this gets upstreamed quickly, but until then it's probably very broken and not something I'd put into production.
