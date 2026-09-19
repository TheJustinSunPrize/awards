#!/usr/bin/env python3
"""Linux x86_64 only: add a process-inherited seccomp filter, verify socket creation is
blocked, then exec the requested local command. This restricts the process; it does
not create a network namespace. Standard output/error remain ordinary inherited FDs.
"""
import ctypes, errno, os, platform, socket, sys
if platform.system()!='Linux' or platform.machine()!='x86_64':
 raise RuntimeError('This syscall filter is only defined for Linux x86_64')
class SockFilter(ctypes.Structure):
 _fields_=[('code',ctypes.c_ushort),('jt',ctypes.c_ubyte),('jf',ctypes.c_ubyte),('k',ctypes.c_uint)]
class SockFprog(ctypes.Structure):
 _fields_=[('len',ctypes.c_ushort),('filter',ctypes.POINTER(SockFilter))]
# Classic BPF: ensure x86_64 architecture and reject x32 syscalls, then return EPERM
# for socket/network operations. No changes to system-wide networking are made.
DENIED=[41,42,43,44,45,46,47,49,50,51,52,53,54,55,288,299,307]
ins=[(0x20,0,0,4),(0x15,1,0,0xc000003e),(0x06,0,0,0x80000000),
     (0x20,0,0,0),(0x35,0,1,0x40000000),(0x06,0,0,0x00050000|errno.EPERM)]
for nr in DENIED: ins.extend([(0x15,0,1,nr),(0x06,0,0,0x00050000|errno.EPERM)])
ins.append((0x06,0,0,0x7fff0000))
arr=(SockFilter*len(ins))(*(SockFilter(*t) for t in ins));prog=SockFprog(len(ins),arr)
libc=ctypes.CDLL(None,use_errno=True)
if libc.prctl(38,1,0,0,0)!=0: raise OSError(ctypes.get_errno(),'PR_SET_NO_NEW_PRIVS failed')
if libc.prctl(22,2,ctypes.byref(prog),0,0)!=0: raise OSError(ctypes.get_errno(),'PR_SET_SECCOMP failed')
for family in [socket.AF_INET,socket.AF_INET6]:
 try:
  s=socket.socket(family,socket.SOCK_STREAM)
 except PermissionError as e:
  if e.errno!=errno.EPERM: raise
 else:
  s.close();raise RuntimeError('Network socket unexpectedly allowed')
print('SECCOMP_GUARD: IPv4 and IPv6 socket creation verified denied (EPERM).',file=sys.stderr,flush=True)
if len(sys.argv)<2: raise SystemExit('Expected a command')
os.execvpe(sys.argv[1],sys.argv[1:],os.environ)
