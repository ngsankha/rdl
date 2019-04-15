RDL.nowrap :Process

RDL.type :Process, 'self.abort', '(?String msg) -> %any'
RDL.type :Process, 'self.argv0', '() -> String frozen_string'
RDL.type :Process, 'self.clock_getres', '(Symbol or Integer clock_id, ?Symbol unit) -> Float or Integer'
RDL.type :Process, 'self.clock_gettime', '(Symbol or Integer clock_id, ?Symbol unit) -> Float or Integer'
RDL.type :Process, 'self.daemon', '(?%any nochdir, ?%any noclose) -> 0'
RDL.type :Process, 'self.detach', '(Integer pid) -> Thread'
RDL.type :Process, 'self.egid', '() -> Integer'
RDL.type :Process, 'self.egid=', '(Integer) -> Integer'
RDL.type :Process, 'self.euid', '() -> Integer'
RDL.type :Process, 'self.euid=', '(Integer) -> Integer user'
  #RDL.type :Process, 'self.exec', '(env: ?Hash<String, String>, command:String, args:*String) -> %any' # TODO: env
RDL.type :Process, 'self.exit', '(?Integer status) -> %any'
RDL.type :Process, 'self.exit!', '(?Integer status) -> %any'
RDL.type :Process, 'self.fork', '() -> Integer or nil'
RDL.type :Process, 'self.fork', '() { () -> %any } -> Integer or nil'
RDL.type :Process, 'self.getpgid', '(Integer pid) -> Integer'
RDL.type :Process, 'self.getpgrp', '() -> Integer'
RDL.type :Process, 'self.getpriority', '(Integer kind, Integer) -> Integer'
RDL.type :Process, 'self.getrlimit', '(Symbol or String or Integer resource) -> [Integer, Integer] cur_max_limit'
RDL.type :Process, 'self.getsid', '(?Integer pid) -> Integer'
RDL.type :Process, 'self.gid', '() -> Integer'
RDL.type :Process, 'self.gid=', '(Integer) -> Integer'
RDL.type :Process, 'self.groups', '() -> Array<Integer>'
RDL.type :Process, 'self.groups=', '(Array<Integer>) -> Array<Integer>'
RDL.type :Process, 'self.initgroups', '(String username, Integer gid) -> Array<Integer>'
RDL.type :Process, 'self.kill', '(Integer or Symbol or String signal, *Integer pids) -> Integer'
RDL.type :Process, 'self.maxgroups', '() -> Integer'
RDL.type :Process, 'self.maxgroups=', '(Integer) -> Integer'
RDL.type :Process, 'self.pid', '() -> Integer'
RDL.type :Process, 'self.ppid', '() -> Integer'
RDL.type :Process, 'self.setpriority', '(Integer kind, Integer, Integer priority) -> 0'
RDL.type :Process, 'self.setproctitle', '(String) -> String'
RDL.type :Process, 'self.setrlimit', '(Symbol or String or Integer resource, Integer cur_limit, ?Integer max_limit) -> nil'
RDL.type :Process, 'self.setpgid', '(Integer pid, Integer) -> Integer'
RDL.type :Process, 'self.setsid', '() -> Integer'
  #RDL.type :Process, 'self.spawn', '(?Hash<String, String> env, String command, *String args) -> %any' # TODO: env
RDL.type :Process, 'self.times', '() -> Process::Tms'
RDL.type :Process, 'self.uid', '() -> Integer'
RDL.type :Process, 'self.uid=', '(Integer user) -> Integer'
RDL.type :Process, 'self.wait', '(?Integer pid, ?Integer flags) -> Integer'
RDL.type :Process, 'self.wait2', '(?Integer pid, ?Integer flags) -> [Integer, Integer] pid_and_status'
RDL.type :Process, 'self.waitall', '() -> Array<[Integer, Integer]>'
RDL.type :Process, 'self.waitpid', '(?Integer pid, ?Integer flags) -> Integer'
RDL.type :Process, 'self.waitpid2', '(?Integer pid, ?Integer flags) -> [Integer, Integer] pid_and_status'

RDL.nowrap :'Process::GID'
RDL.type :'Process::GID', 'self.change_privilege', '(Integer group) -> Integer'
RDL.type :'Process::GID', 'self.eid', '() -> Integer'
RDL.type :'Process::GID', 'self.from_name', '(String name) -> Integer gid'
RDL.type :'Process::GID', 'self.grant_privilege', '(Integer group) -> Integer'
RDL.rdl_alias :'Process::GID', 'self.eid=', 'self.grant_privilege'
RDL.type :'Process::GID', 'self.re_exchange', '() -> Integer'
RDL.type :'Process::GID', 'self.re_exchangeable?', '() -> %bool'
RDL.type :'Process::GID', 'self.rid', '() -> Integer'
RDL.type :'Process::GID', 'self.sid_available?', '() -> %bool'
RDL.type :'Process::GID', 'self.switch', '() -> Integer'
RDL.type :'Process::GID', 'self.switch', '() { () -> t } -> t'

RDL.nowrap :'Process::UID'
RDL.type :'Process::UID', 'self.change_privilege', '(Integer user) -> Integer'
RDL.type :'Process::UID', 'self.eid', '() -> Integer'
RDL.type :'Process::UID', 'self.from_name', '(String name) -> Integer uid'
RDL.type :'Process::UID', 'self.grant_privilege', '(Integer user) -> Integer'
RDL.rdl_alias :'Process::UID', 'self.eid=', 'self.grant_privilege'
RDL.type :'Process::UID', 'self.re_exchange', '() -> Integer'
RDL.type :'Process::UID', 'self.re_exchangeable?', '() -> %bool'
RDL.type :'Process::UID', 'self.rid', '() -> Integer'
RDL.type :'Process::UID', 'self.sid_available?', '() -> %bool'
RDL.type :'Process::UID', 'self.switch', '() -> Integer'
RDL.type :'Process::UID', 'self.switch', '() { () -> t } -> t'

RDL.nowrap :'Process::Status'
 RDL.type :'Process::Status', :&, '(Integer num) -> Integer'
 RDL.type :'Process::Status', :==, '(%any other) -> %bool'
 RDL.type :'Process::Status', :>>, '(Integer num) -> Integer'
 RDL.type :'Process::Status', :coredump?, '() -> %bool'
 RDL.type :'Process::Status', :exited?, '() -> %bool'
 RDL.type :'Process::Status', :exitstatus, '() -> Integer or nil'
 RDL.type :'Process::Status', :inspect, '() -> String'
 RDL.type :'Process::Status', :pid, '() -> Integer'
 RDL.type :'Process::Status', :signaled?, '() -> %bool'
 RDL.type :'Process::Status', :stopped?, '() -> %bool'
 RDL.type :'Process::Status', :stopsig, '() -> Integer or nil'
 RDL.type :'Process::Status', :success?, '() -> %bool'
 RDL.type :'Process::Status', :termsig, '() -> Integer or nil'
 RDL.type :'Process::Status', :to_i, '() -> Integer'
RDL.rdl_alias :'Process::Status', :to_int, :to_i
RDL.type :'Process::Status', :to_s, '() -> String'

RDL.nowrap :'Process::Sys'
RDL.type :'Process::Sys', 'self.geteuid', '() -> Integer'
RDL.type :'Process::Sys', 'self.getgid', '() -> Integer'
RDL.type :'Process::Sys', 'self.getuid', '() -> Integer'
RDL.type :'Process::Sys', 'self.issetugid', '() -> %bool'
RDL.type :'Process::Sys', 'self.setegid', '(Integer group) -> nil'
RDL.type :'Process::Sys', 'self.seteuid', '(Integer user) -> nil'
RDL.type :'Process::Sys', 'self.setgid', '(Integer group) -> nil'
RDL.type :'Process::Sys', 'self.setregid', '(Integer rid, Integer eid) -> nil'
RDL.type :'Process::Sys', 'self.setresgid', '(Integer rid, Integer eid, Integer sid) -> nil'
RDL.type :'Process::Sys', 'self.setresuid', '(Integer rid, Integer eid, Integer sid) -> nil'
RDL.type :'Process::Sys', 'self.setreuid', '(Integer rid, Integer eid) -> nil'
RDL.type :'Process::Sys', 'self.setrgid', '(Integer group) -> nil'
RDL.type :'Process::Sys', 'self.setruid', '(Integer user) -> nil'
RDL.type :'Process::Sys', 'self.setuid', '(Integer user) -> nil'

RDL.nowrap :'Process::Waiter'
RDL.type :'Process::Waiter', 'pid', '() -> Integer'
