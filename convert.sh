#!/bin/bash

cp -r templates/highlight docs/highlight

python compile_html_template.py test templates/pd_template.html templates/style.css sub_template.html

# Convert Markdown files to HTML using Pandoc
for md_file in $(find docs -type f -name "*.md"); do
    html_file="${md_file%.md}.html"
    pandoc --ascii --template sub_template.html "$md_file" -o "$html_file"
    if [ $? != 0 ] ; then 
        echo $md_file
        break
    fi

    sed -i 's/^\s*<span/<span/g' $html_file
    sed -i 's/^\s*\([^<]\)/\1/g' $html_file
done

rm sub_template.html

echo "Markdown to HTML conversion complete."
