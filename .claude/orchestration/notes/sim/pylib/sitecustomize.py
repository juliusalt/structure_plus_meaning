"""The simulation's clock for every Python process of its world: SIM_CLOCK names one file holding the simulated epoch,
read at every call, which only moves forward — the driver sets it at each step, and the fake claude moves it past each
session's last reply (a session takes time: a reply stamped after the start its caller recorded, and the next session
starting after it). File times are set by the driver."""
import os
import time as _time

_path = os.environ.get("SIM_CLOCK")
if _path and os.path.exists(_path):
    _localtime, _gmtime, _strftime, _ctime, _asctime = (_time.localtime, _time.gmtime, _time.strftime,
                                                         _time.ctime, _time.asctime)
    _count = [0]

    def time():
        _count[0] += 1
        try:
            with open(_path) as f:
                return float(f.read().split()[0]) + _count[0] * 1e-6
        except (OSError, ValueError, IndexError):
            return 0.0

    def time_ns():
        return int(time() * 1e9) + os.getpid() % 1000

    def localtime(secs=None):
        return _localtime(time() if secs is None else secs)

    def gmtime(secs=None):
        return _gmtime(time() if secs is None else secs)

    def strftime(fmt, t=None):
        return _strftime(fmt, localtime() if t is None else t)

    def ctime(secs=None):
        return _ctime(time() if secs is None else secs)

    def asctime(t=None):
        return _asctime(localtime() if t is None else t)

    _time.time, _time.time_ns, _time.localtime, _time.gmtime = time, time_ns, localtime, gmtime
    _time.strftime, _time.ctime, _time.asctime = strftime, ctime, asctime
    import datetime as _dt

    class _DateTime(_dt.datetime):
        @classmethod
        def now(cls, tz=None):
            return cls.fromtimestamp(time(), tz)

        @classmethod
        def utcnow(cls):
            return cls.utcfromtimestamp(time())

        @classmethod
        def today(cls):
            return cls.fromtimestamp(time())
    _dt.datetime = _DateTime
