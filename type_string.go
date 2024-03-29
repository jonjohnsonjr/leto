// Code generated by "stringer -type=Type"; DO NOT EDIT.

package leto

import "strconv"

func _() {
	// An "invalid array index" compiler error signifies that the constant values have changed.
	// Re-run the stringer command to generate them again.
	var x [1]struct{}
	_ = x[INVALID-0]
	_ = x[BOOL-1]
	_ = x[INT64-2]
	_ = x[FLOAT64-3]
	_ = x[STRING-4]
	_ = x[BOOLSLICE-5]
	_ = x[INT64SLICE-6]
	_ = x[FLOAT64SLICE-7]
	_ = x[STRINGSLICE-8]
}

const _Type_name = "INVALIDBOOLINT64FLOAT64STRINGBOOLSLICEINT64SLICEFLOAT64SLICESTRINGSLICE"

var _Type_index = [...]uint8{0, 7, 11, 16, 23, 29, 38, 48, 60, 71}

func (i Type) String() string {
	if i < 0 || i >= Type(len(_Type_index)-1) {
		return "Type(" + strconv.FormatInt(int64(i), 10) + ")"
	}
	return _Type_name[_Type_index[i]:_Type_index[i+1]]
}

func ParseType(s string) Type {
	maxLen := len(_Type_name)
	for i, idx := range _Type_index {
		end := int(idx)+len(s)
		if end > maxLen {
			return Type(0)
		}
		if s == _Type_name[idx:end] {
			return Type(i)
		}
	}

	return Type(0)
}
