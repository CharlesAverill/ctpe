#!/bin/bash

# Convert Markdown files to HTML using Pandoc
for md_file in $(find docs -type f -name "*.md"); do
    html_file="${md_file%.md}.html"
    pandoc --ascii "$md_file" -o "$html_file"
done

echo "Markdown to HTML conversion complete."
