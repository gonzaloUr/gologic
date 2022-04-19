package gologic

type Number interface {
	~uint | ~int | ~uint8 | ~uint16 | ~uint32 | ~uint64 | ~int8 |
		~int16 | ~int32 | ~int64 | ~float32 | ~float64
}

func max[T Number](a, b T) T {
	if a > b {
		return a
	}
	return b
}

func min[T Number](a, b T) T {
	if a > b {
		return b
	}
	return a
}
