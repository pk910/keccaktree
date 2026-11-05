module github.com/pk910/keccaktree/bench

go 1.22.2

require (
	github.com/pk910/hashtree-bindings v0.2.7-0.20260923072618-bd6eb1c79200
	github.com/pk910/keccaktree v0.0.0
	golang.org/x/crypto v0.31.0
)

require (
	github.com/klauspost/cpuid/v2 v2.3.0 // indirect
	golang.org/x/sys v0.30.0 // indirect
)

replace github.com/pk910/keccaktree => ../
