/**
 * MerLean Blog — post listing and rendering.
 *
 * To add a new post:
 *   1. Create a Markdown file in the blogs/ folder (e.g. 2026-04-01-my-post.md)
 *   2. Add an entry to the blogPosts array below.
 */

const blogPosts = [
  {
    file:    "blog1.md",
    title:   "Autoformalization as automated refereeing: MerLean catches errors in a frontier quantum computing paper",
    date:    "2026-03-14",
    excerpt: "We evaluated MerLean on \"Balanced Product Quantum Codes\" and discovered actual mathematical errors that had slipped past peer review — caught by a tug-of-war between the Lean compiler and our faithfulness checker."
  }
];

function formatDate(dateStr) {
  const d = new Date(dateStr + "T00:00:00");
  return d.toLocaleDateString("en-US", { year: "numeric", month: "long", day: "numeric" });
}

function loadBlogPosts() {
  const container = document.getElementById("blog-list");
  if (!container) return;

  if (blogPosts.length === 0) {
    container.innerHTML = '<p class="blog-empty">No blog posts yet. Stay tuned!</p>';
    return;
  }

  // Sort newest first
  const sorted = blogPosts.slice().sort((a, b) => b.date.localeCompare(a.date));

  container.innerHTML = sorted
    .map(
      (post) => `
    <article class="blog-card">
      <a href="blog-post.html?post=${encodeURIComponent(post.file)}" class="blog-card-link">
        <time class="blog-date">${formatDate(post.date)}</time>
        <h3 class="blog-card-title">${post.title}</h3>
        <p class="blog-card-excerpt">${post.excerpt}</p>
        <span class="blog-read-more">Read more &rarr;</span>
      </a>
    </article>`
    )
    .join("");
}

document.addEventListener("DOMContentLoaded", loadBlogPosts);
