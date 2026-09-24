"""Run the real console main/handlers over pipes for isolated tests with no loopback networking.

Only HTTPServer's byte transport changes. Authentication, routing, rendering, controls and the production reload
loop are the real ones. A request is an HTTP byte string carried inside one JSON line; a reply carries the response
bytes the real BaseHTTPRequestHandler wrote. This is test infrastructure, not an alternate console implementation.
"""
import io
import json
import os
from pathlib import Path
import select
import sys

HERE=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(HERE))
import dashboard


class Connection:
    def __init__(self,data):self.input=io.BytesIO(data);self.output=bytearray()
    def makefile(self,*args,**kwargs):return self.input
    def sendall(self,data):self.output.extend(data)


class PipeServer:
    def __init__(self,address,handler):
        self.server_address=(address[0],address[1] or 8765)
        self.handler=handler
        self.running=True
    def serve_forever(self):
        while self.running:
            ready,_,_=select.select([sys.stdin],[],[],0.1)
            if not ready:continue
            line=sys.stdin.readline()
            if not line:return
            request=Connection(json.loads(line)['request'].encode())
            self.handler(request,('127.0.0.1',0),self)
            print(json.dumps({'response':bytes(request.output).decode()}),flush=True)
    def shutdown(self):self.running=False
    def server_close(self):pass


dashboard.Server=PipeServer
execv=os.execv
def reload_transport(executable,args):
    execv(executable,[executable,str(Path(__file__).resolve()),*args[2:]])
dashboard.os.execv=reload_transport
raise SystemExit(dashboard.main())
