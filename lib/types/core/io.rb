RDL.nowrap :IO # Do not wrap this class. Leads to mysterious errors.

RDL.type :IO, :initialize, '(Integer fd, ?Integer mode, ?Integer opt) -> self'
RDL.type :IO, 'self.binread', '(String name, ?Integer length, ?Integer offset) -> String'
RDL.type :IO, 'self.binwrite', '(String name, String, ?Integer offset, %open_args) -> Integer'
RDL.type :IO, 'self.copy_stream', '(String or IO src, String or IO dst, ?Integer copy_length, ?Integer src_offset) -> Integer'
RDL.rdl_alias :IO, 'self.for_fd', 'initialize'
RDL.type :IO, 'self.foreach', '(String name, ?String sep, ?Integer limit, %open_args) { (String) -> %any } -> nil'
RDL.type :IO, 'self.foreach', '(String name, ?String sep, ?Integer limit, %open_args) -> Enumerator<String>'
RDL.type :IO, 'self.open', '(Integer fd, ?String mode, %open_args) -> IO'
RDL.type :IO, 'self.open', '(Integer fd, ?String mode, %open_args) { (IO) -> t } -> t'
RDL.type :IO, 'self.pipe', '(?String ext_or_ext_int_enc, %open_args) -> [IO, IO]'
RDL.type :IO, 'self.pipe', '(?String ext_enc, ?String int_enc, %open_args) -> [IO, IO]'
RDL.type :IO, 'self.pipe', '(?String ext_or_ext_int_enc, %open_args) { ([IO, IO]) -> t } -> t'
RDL.type :IO, 'self.pipe', '(?String ext_enc, ?String int_enc, %open_args) { ([IO, IO]) -> t } -> t'
RDL.type :IO, 'self.popen', '(?Hash<String, String> env, String cmd, ?String mode, %open_args) -> IO'
RDL.type :IO, 'self.popen', '(?Hash<String, String> env, String cmd, ?String mode, %open_args) { (IO) -> t } -> t'
RDL.type :IO, 'self.read', '(String name, ?Integer length, ?Integer offset, %open_args) -> String'
RDL.type :IO, 'self.readlines', '(String name, ?String sep, ?Integer limit, %open_args) -> Array<String>'
RDL.type :IO, 'self.select', '(Array<IO> read_array, ?Array<IO> write_array, ?Array<IO> error_array, ?Integer timeout) -> Array<IO> or nil'
RDL.type :IO, 'self.sysopen', '(String path, ?String mode, ?String perm) -> Integer' # TODO unsure of RDL.type of perm
RDL.type :IO, 'self.try_convert', '([to_io: () -> IO]) -> IO or nil'
RDL.type :IO, 'self.write', '(String name, String, ?Integer offset, %open_args) -> Integer'
RDL.type :IO, :<<, '([to_s: () -> String]) -> self'
RDL.type :IO, :advise, '(:normal or :sequence or :random or :willneed or :dontneed or :noreuse, ?Integer offset, ?Integer len) -> nil'
RDL.type :IO, :autoclose=, '(%bool) -> %bool'
RDL.type :IO, :autoclose?, '() -> %bool'
RDL.type :IO, :binmode, '() -> self'
RDL.type :IO, :binmode?, '() -> %bool'
RDL.rdl_alias :IO, :bytes, :each_byte # deprecated
RDL.rdl_alias :IO, :chars, :each_char # deprecated
RDL.type :IO, :close, '() -> nil'
RDL.type :IO, :close_on_exec=, '(%bool) -> %bool'
RDL.type :IO, :close_on_exec?, '() -> %bool'
RDL.type :IO, :close_read, '() -> nil'
RDL.type :IO, :close_write, '() -> nil'
RDL.type :IO, :closed?, '() -> %bool'
RDL.rdl_alias :IO, :codepoints, :each_codepoint # deprecated
RDL.type :IO, :each, '(?String sep, ?Integer limit) { (String) -> %any } -> self'
RDL.type :IO, :each, '(?String sep, ?Integer limit) -> Enumerator<String>'
RDL.rdl_alias :IO, :each_line, :each
RDL.type :IO, :each_byte, '() { (Integer) -> %any } -> self'
RDL.type :IO, :each_byte, '() -> Enumerator<Integer>'
RDL.type :IO, :each_char, '() { (String) -> %any } -> self'
RDL.type :IO, :each_char, '() -> Enumerator<String>'
RDL.type :IO, :each_codepoint, '() { (Integer) -> %any } -> self'
RDL.type :IO, :each_codepoint, '() -> Enumerator<Integer>'
RDL.type :IO, :eof, '() -> %bool'
RDL.rdl_alias :IO, :eof?, :eof
RDL.type :IO, :external_enconding, '() -> Enconding'
RDL.type :IO, :fcntl, '(Integer integer_cmd, String or Integer arg) -> Integer'
RDL.type :IO, :fdatasync, '() -> 0 or nil'
RDL.type :IO, :fileno, '() -> Integer'
RDL.type :IO, :flush, '() -> self'
RDL.type :IO, :fsync, '() -> 0 or nil'
RDL.type :IO, :getbyte, '() -> Integer or nil'
RDL.type :IO, :getc, '() -> String or nil'
RDL.type :IO, :gets, '(?String sep, ?Integer limit) -> String or nil'
RDL.type :IO, :inspect, '() -> String'
RDL.type :IO, :internal_encoding, '() -> Encoding'
RDL.type :IO, :ioctl, '(Integer integer_cmd, String or Integer arg) -> Integer'
RDL.type :IO, :isatty, '() -> %bool'
RDL.type :IO, :lineno, '() -> Integer'
RDL.type :IO, :lineno=, '(Integer) -> Integer'
RDL.rdl_alias :IO, :lines, :each_line # deprecated
RDL.type :IO, :pid, '() -> Integer'
RDL.type :IO, :pos, '() -> Integer'
RDL.type :IO, :pos=, '(Integer) -> Integer'
RDL.type :IO, :print, '(*[to_s: () -> String]) -> nil'
RDL.type :IO, :printf, '(String format_string, *%any) -> nil'
RDL.type :IO, :putc, '(Numeric or String) -> %any'
RDL.type :IO, :puts, '(*[to_s: () -> String]) -> nil'
RDL.type :IO, :read, '(?Integer length, ?String outbuf) -> String or nil'
RDL.type :IO, :read_nonblock, '(Integer maxlen) -> String'
RDL.type :IO, :read_nonblock, '(Integer maxlen, String outbuf) -> String outbuf'
RDL.type :IO, :readbyte, '() -> Integer'
RDL.type :IO, :readchar, '() -> String'
RDL.type :IO, :readline, '(?String sep, ?Integer limit) -> String'
RDL.type :IO, :readlines, '(?String sep, ?Integer limit) -> Array<String>'
RDL.type :IO, :readpartial, '(Integer maxlen) -> String'
RDL.type :IO, :readpartial, '(Integer maxlen, String outbuf) -> String outbuf'
RDL.type :IO, :reopen, '(IO other_IO) -> IO'
RDL.type :IO, :reopen, '(String path, String mode_str) -> IO'
RDL.type :IO, :rewind, '() -> 0'
RDL.type :IO, :seek, '(Integer amount, ?Integer whence) -> 0'
RDL.type :IO, :set_encoding, '(?String or Encoding ext_or_ext_int_enc) -> self'
RDL.type :IO, :set_encoding, '(?String or Encoding ext_enc, ?String or Encoding int_enc) -> self'
RDL.type :IO, :stat, '() -> File::Stat'
RDL.type :IO, :sync, '() -> %bool'
RDL.type :IO, :sync=, '(%bool) -> %bool'
RDL.type :IO, :sysread, '(Integer maxlen, String outbuf) -> String'
RDL.type :IO, :sysseek, '(Integer amount, ?Integer whence) -> Integer'
RDL.type :IO, :syswrite, '(String) -> Integer'
RDL.type :IO, :tell, '() -> Integer'
RDL.rdl_alias :IO, :to_i, :fileno
RDL.type :IO, :to_io, '() -> self'
RDL.type :IO, :tty?, '() -> %bool'
RDL.type :IO, :ungetbyte, '(String or Integer) -> nil'
RDL.type :IO, :ungetc, '(String) -> nil'
RDL.type :IO, :write, '(String) -> Integer'
RDL.type :IO, :write_nonbloc, '(String, ?Integer options) -> Integer'
