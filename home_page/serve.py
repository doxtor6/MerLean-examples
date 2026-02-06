"""Local preview server for the MerLean home page.

Processes Liquid-style templates and serves the site locally.
Usage: python serve.py [port]
"""

import http.server
import os
import re
import sys

PORT = int(sys.argv[1]) if len(sys.argv) > 1 else 4000
SITE_DIR = os.path.dirname(os.path.abspath(__file__))
BUILD_DIR = os.path.join(SITE_DIR, "_site")

# Site config values (mirrors _config.yml)
CONFIG = {
    "site.title": "MerLean",
    "site.description": "An Agentic Framework for Autoformalization in Quantum Computation",
    "site.url": "https://doxtor6.github.io/MerLean-examples",
    "site.baseurl": "",
    "site.github_username": "doxtor6",
    "site.repository": "doxtor6/MerLean-examples",
}


def read_layout(name):
    path = os.path.join(SITE_DIR, "_layouts", f"{name}.html")
    with open(path, "r", encoding="utf-8") as f:
        return f.read()


def process_template(html):
    """Simple Liquid template processor."""
    # Remove {% seo %} tag (not needed for local preview)
    html = re.sub(r"\{%\s*seo\s*%\}", "", html)

    # Remove {% if %} / {% endif %} blocks we don't need
    html = re.sub(r"\{%.*?%\}", "", html)

    # Replace {{ var }} with config values
    def replace_var(match):
        expr = match.group(1).strip()

        # Handle relative_url filter
        expr = re.sub(r"\s*\|\s*relative_url\s*$", "", expr)

        # Handle string literals with append filters
        append_match = re.match(r"'([^']*)'(?:\s*\|\s*append:\s*(?:site\.\w+|'[^']*'))*", expr)
        if append_match:
            return append_match.group(1)

        # Handle page.X or site.X
        if expr.startswith("page."):
            key = expr.replace("page.", "site.")
            return CONFIG.get(key, "")

        return CONFIG.get(expr, "")

    html = re.sub(r"\{\{\s*(.*?)\s*\}\}", replace_var, html)
    return html


def build_page(src_path, layout_name="default"):
    """Read a page file and wrap it in its layout."""
    with open(src_path, "r", encoding="utf-8") as f:
        raw = f.read()

    # Strip front matter
    if raw.startswith("---"):
        _, _, content = raw.split("---", 2)
    else:
        content = raw

    layout = read_layout(layout_name)
    html = layout.replace("{{ content }}", content)
    return process_template(html)


def build_site():
    """Build all pages into _site directory."""
    os.makedirs(BUILD_DIR, exist_ok=True)

    # Copy assets
    assets_src = os.path.join(SITE_DIR, "assets")
    assets_dst = os.path.join(BUILD_DIR, "assets")
    if os.path.exists(assets_src):
        import shutil
        if os.path.exists(assets_dst):
            shutil.rmtree(assets_dst)
        shutil.copytree(assets_src, assets_dst)

    # Build index.html
    index_src = os.path.join(SITE_DIR, "index.html")
    if os.path.exists(index_src):
        html = build_page(index_src)
        with open(os.path.join(BUILD_DIR, "index.html"), "w", encoding="utf-8") as f:
            f.write(html)

    # Build 404.html
    page_404 = os.path.join(SITE_DIR, "404.html")
    if os.path.exists(page_404):
        html = build_page(page_404)
        with open(os.path.join(BUILD_DIR, "404.html"), "w", encoding="utf-8") as f:
            f.write(html)


def main():
    build_site()
    os.chdir(BUILD_DIR)

    handler = http.server.SimpleHTTPRequestHandler
    with http.server.HTTPServer(("", PORT), handler) as httpd:
        print(f"\n  MerLean home page preview")
        print(f"  Serving at: http://localhost:{PORT}")
        print(f"  Press Ctrl+C to stop\n")
        try:
            httpd.serve_forever()
        except KeyboardInterrupt:
            print("\nStopped.")


if __name__ == "__main__":
    main()
