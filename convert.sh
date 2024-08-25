#!/bin/bash

# Copy highlight template
cp -r templates/highlight docs/highlight

# Compile HTML template
python compile_html_template.py $1 templates/pd_template.html templates/style.css sub_template.html

# Find all Markdown files
md_files=($(find docs -type f -name "*.md"))
total_files=${#md_files[@]}

# Function to display progress
progress() {
    local current=$1
    local total=$2
	local file=$3
    local percent=$((current * 100 / total))
    printf "\rProgress: [%-50s] %d%% - %-*s" "$(printf "%0.s#" $(seq 1 $((percent / 2))))" "$percent" 50 "$file"
}

# Convert Markdown files to HTML using Pandoc
i=0
for md_file in "${md_files[@]}"; do
    html_file="${md_file%.md}.html"
    pandoc --ascii --preserve-tabs --template sub_template.html "$md_file" -o "$html_file"
    if [ $? != 0 ] ; then 
        echo "$md_file conversion failed"
        break
    fi

    i=$((i + 1))
    progress $i $total_files $md_file
done
echo

# Clean up
rm sub_template.html

echo "Markdown to HTML conversion complete."

