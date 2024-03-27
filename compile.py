import os
import shutil

def compile_markdown(file_path, docs_dir):
    with open(file_path, 'r') as file:
        lines = file.readlines()
    
    compiled_lines = []
    for line in lines:
        if line.startswith("#include"):
            included_file_path = line.split("#include")[1].strip()
            if included_file_path.startswith('/'):
                included_file_path = included_file_path[1:]
            included_file_path = os.path.join(os.path.dirname(file_path), included_file_path)
            compiled_lines.extend(compile_markdown(included_file_path, docs_dir))
        else:
            compiled_lines.append(line)
    
    with open(file_path, 'w') as file:
        file.writelines(compiled_lines)
    
    return compiled_lines

def backup_docs(docs_dir):
    if os.path.exists(docs_dir):
        shutil.make_archive(docs_dir, "zip", docs_dir)
        shutil.rmtree(docs_dir)

def copy_source_to_docs(source_dir, docs_dir):
    shutil.copytree(source_dir, docs_dir)

def rename_template_to_index(docs_dir):
    os.rename(os.path.join(docs_dir, "template.md"), os.path.join(docs_dir, "index.md"))

if __name__ == "__main__":
    source_dir = "source"
    docs_dir = "docs"
    
    backup_docs(docs_dir)
    copy_source_to_docs(source_dir, docs_dir)
    
    template_path = os.path.join(docs_dir, "template.md")
    compile_markdown(template_path, docs_dir)
    rename_template_to_index(docs_dir)
    
    print("Compilation complete. Output written to docs/index.md")
