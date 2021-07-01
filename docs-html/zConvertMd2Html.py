#!/usr/bin/env python3

# If you want to browse the Carp documentation offline with all the bells and whistles 
# (e.g. working hyperlinks to other documents and embedded graphics) that are usually 
# provided by the github webpage, you can convert it to static html with this script.
#
# It needs Python3 to work.
# 
# Start the conversion with:
#     python3 zConvertMd2Html.py 
# or depending on you system configuration (e.g. on Windows):
#     python zConvertMd2Html.py
# or by executing the script itself (only on *NIX / BSD):
#     chmod u+x zConvertMd2Html.py
#     ./zConvertMd2Html.py
#
# Please note: 
#    inter-document references do not work since the markdown-library does not create 
#    the required html-anchor elements for headings like github does. 

import glob, os, platform, shutil

# some definitions
docPath = "../docs/"
docPathLen = len(docPath)

def execute( cmd ):
    if platform.system()=="Windows":
        cmd = cmd.replace("/","\\")
    # TODO: use subprocess.run() instead, check return-code==0, otherwise abort program
    os.system(cmd)
    
def generate(fnInput, fnBase4Output):
    if not os.path.isfile(fnInput):
        print( "copying directory: %s to %s" % (fnInput,fnBase4Output) )
        shutil.copytree( fnInput, fnBase4Output)
    elif fnInput.endswith(".md"):
        # converting to html
        with open(fnInput) as finput:
            content = finput.read()
        fnOutput = fnBase4Output[:-3] + '.html'
        execute( "./out/zConvertMd2Html.exe %s %s" % (fnInput, fnOutput) )
    else:
        # any other files might be resources (e.g. pictures) which probably need to be copied
        print( "copying file: %s to %s" % (fnInput,fnBase4Output) )
        shutil.copy( fnInput, fnBase4Output)

def remove_existing_dir(path):
    if os.path.exists(path):
        shutil.rmtree(path)


def main():
    print("building the converter")
    execute("carp -b zConvertMd2Html.carp")    
    
    print("(re)generating html docs for Carp standard library...")
    pOld = os.getcwd()
    os.chdir("..")
    cmd = "carp -x ./docs/core/generate_core_docs.carp"
    execute(cmd)    
    os.chdir(pOld)
    print("... done\n")

    for p in glob.glob("./*/"):
        if (not "out" in p) and not ("lib" in p):
            remove_existing_dir(p)

    # generate html files
    for fname in glob.glob(docPath+"*"):
        generate( fname, fname[docPathLen:] )
    generate( "./core/README.md", "./core/README.md" )
    print("\ndone :-)")

# main program
main()
