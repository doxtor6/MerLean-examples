"""Local preview server for the MerLean home page.

Serves static files directly — no template processing needed.
The /hidden/ path is accessible by direct URL but not linked in the UI.

Usage: python serve.py [port]
"""

import http.server
import os
import sys

PORT = int(sys.argv[1]) if len(sys.argv) > 1 else 4000
SITE_DIR = os.path.dirname(os.path.abspath(__file__))


class MerLeanHandler(http.server.SimpleHTTPRequestHandler):
    """Serve static files from the home_page directory."""

    def __init__(self, *args, **kwargs):
        super().__init__(*args, directory=SITE_DIR, **kwargs)

    def end_headers(self):
        # Allow large video files to stream properly
        self.send_header('Accept-Ranges', 'bytes')
        super().end_headers()


def main():
    with http.server.HTTPServer(("", PORT), MerLeanHandler) as httpd:
        print(f"\n  ✦ MerLean — Local Preview")
        print(f"  ─────────────────────────")
        print(f"  Main site:  http://localhost:{PORT}")
        print(f"  Hidden vid: http://localhost:{PORT}/hidden/intro.mp4")
        print(f"  Press Ctrl+C to stop\n")
        try:
            httpd.serve_forever()
        except KeyboardInterrupt:
            print("\nStopped.")


if __name__ == "__main__":
    main()
