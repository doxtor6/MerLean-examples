/**
 * MerLean Blog — individual post viewer.
 * Fetches a Markdown file from blogs/ and renders it with marked.js.
 */

function loadPost() {
  const params  = new URLSearchParams(window.location.search);
  const file    = params.get("post");
  const content = document.getElementById("post-content");
  const title   = document.getElementById("post-title");

  if (!file) {
    content.innerHTML = '<p>Post not found. <a href="blog.html">Back to blog</a></p>';
    return;
  }

  fetch("blogs/" + file)
    .then((res) => {
      if (!res.ok) throw new Error("Not found");
      return res.text();
    })
    .then((md) => {
      // Extract title from first # heading, or fall back to blogPosts metadata
      const titleMatch = md.match(/^#\s+(.+)$/m);
      var postTitle = titleMatch ? titleMatch[1] : null;
      if (!postTitle && typeof blogPosts !== "undefined") {
        const meta = blogPosts.find((p) => p.file === file);
        if (meta) postTitle = meta.title;
      }
      if (postTitle) {
        title.textContent = postTitle;
        document.title    = postTitle + " — MerLean Blog";
      }

      // Extract date from filename
      const dateMatch = file.match(/^(\d{4}-\d{2}-\d{2})/);
      if (dateMatch) {
        const dateEl = document.getElementById("post-date");
        const d = new Date(dateMatch[1] + "T00:00:00");
        dateEl.textContent = d.toLocaleDateString("en-US", {
          year: "numeric", month: "long", day: "numeric"
        });
      }

      content.innerHTML = marked.parse(md);
    })
    .catch(() => {
      content.innerHTML = '<p>Could not load post. <a href="blog.html">Back to blog</a></p>';
    });
}

document.addEventListener("DOMContentLoaded", loadPost);
