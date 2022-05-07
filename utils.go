package gologic

type Number interface {
	~uint | ~int | ~uint8 | ~uint16 | ~uint32 | ~uint64 | ~int8 |
		~int16 | ~int32 | ~int64 | ~float32 | ~float64
}

func max[T Number](args ...T) T {
	var ret = args[0]
	for _, v := range args[1:] {
		if v > ret {
			ret = v
		}
	}
	return ret
}
