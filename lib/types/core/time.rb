rdl_nowrap :Time

type :Time, 'self.at', '(Time) -> Time'
type :Time, 'self.at', '(Numeric seconds_with_frac) -> Time'
type :Time, 'self.at', '(Numeric seconds, Numeric microseconds_with_frac) -> Time'
type :Time, 'self.gm', '(Integer year, ?(Integer or String) month, ?Integer day, ?Integer hour, ?Integer min, ?Numeric sec, ?Numeric usec_with_frac) -> Time'
type :Time, 'self.local', '(Integer year, ?(Integer or String) month, ?Integer day, ?Integer hour, ?Integer min, ?Numeric sec, ?Numeric usec_with_frac) -> Time'
rdl_alias :Time, 'self.mktime', 'self.local'
type :Time, 'self.new', '(?Integer year, ?(Integer or String) month, ?Integer day, ?Integer hour, ?Integer min, ?Numeric sec, ?Numeric usec_with_frac) -> Time'
type :Time, 'self.now', '() -> Time'
type :Time, 'self.utc', '(Integer year, ?(Integer or String) month, ?Integer day, ?Integer hour, ?Integer min, ?Numeric sec, ?Numeric usec_with_frac) -> Time'

type :Time, :+, '(Numeric) -> Time'
type :Time, :-, '(Time) -> Float'
type :Time, :-, '(Numeric) -> Time'
type :Time, :<=>, '(Time other) -> -1 or 0 or 1 or nil'
type :Time, :asctime, '() -> String'
type :Time, :ctime, '() -> String'
type :Time, :day, '() -> Integer'
type :Time, :dst?, '() -> %bool'
type :Time, :eql?, '(%any) -> %bool'
type :Time, :friday?, '() -> %bool'
type :Time, :getgm, '() -> Time'
type :Time, :getlocal, '(?Integer utc_offset) -> Time'
type :Time, :getutc, '() -> Time'
type :Time, :gmt?, '() -> %bool'
type :Time, :gmt_offset, '() -> Integer'
type :Time, :gmtime, '() -> self'
rdl_alias :Time, :gmtoff, :gmt_offset
type :Time, :hash, '() -> Integer'
type :Time, :hour, '() -> Integer'
type :Time, :inspect, '() -> String'
type :Time, :isdst, '() -> %bool'
type :Time, :localtime, '(?String utc_offset) -> self'
type :Time, :mday, '() -> Integer'
type :Time, :min, '() -> Integer'
type :Time, :mon, '() -> Integer'
type :Time, :monday?, '() -> %bool'
rdl_alias :Time, :month, :mon
type :Time, :nsec, '() -> Integer'
type :Time, :round, '(Integer) -> Time'
type :Time, :saturday, '() -> %bool'
type :Time, :sec, '() -> Integer'
type :Time, :strftime, '(String) -> String'
type :Time, :subsec, '() -> Numeric'
type :Time, :succ, '() -> Time'
type :Time, :sunday?, '() -> %bool'
type :Time, :thursday?, '() -> %bool'
type :Time, :to_a, '() -> [Integer, Integer, Integer, Integer, Integer, Integer, Integer, Integer, %bool, String]'
type :Time, :to_f, '() -> Float'
type :Time, :to_i, '() -> Numeric'
type :Time, :to_r, '() -> Rational'
type :Time, :to_s, '() -> String'
type :Time, :tuesday?, '() -> %bool'
type :Time, :tv_nsec, '() -> Numeric'
type :Time, :tv_sec, '() -> Numeric'
type :Time, :tv_usec, '() -> Numeric'
type :Time, :usec, '() -> Numeric'
type :Time, :utc, '() -> self'
type :Time, :utc?, '() -> %bool'
type :Time, :utc_offset, '() -> Integer'
type :Time, :wday, '() -> Integer'
type :Time, :wednesday?, '() -> %bool'
type :Time, :yday, '() -> Integer'
type :Time, :year, '() -> Integer'
type :Time, :zone, '() -> String'