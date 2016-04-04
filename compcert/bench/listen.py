import time
import BaseHTTPServer
import subprocess

HOST_NAME = 'dante.cs.washington.edu' # !!!REMEMBER TO CHANGE THIS!!!
PORT_NUMBER = 9891 # Maybe set this to 9000.


class MyHandler(BaseHTTPServer.BaseHTTPRequestHandler):
    def do_HEAD(s):
        pass
    def do_GET(s):
        pass
    def do_POST(s):
        s.send_response(200)
        s.send_header("Content-type", "text/html")
        s.end_headers()
        subprocess.call("/home/emullen/verso/compcert/bench/run_bench.sh")

if __name__ == '__main__':
    server_class = BaseHTTPServer.HTTPServer
    httpd = server_class((HOST_NAME, PORT_NUMBER), MyHandler)
    print time.asctime(), "Server Starts - %s:%s" % (HOST_NAME, PORT_NUMBER)
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        pass
    httpd.server_close()
    print time.asctime(), "Server Stops - %s:%s" % (HOST_NAME, PORT_NUMBER)


                
