set -x -e

# Build tutorial
cd tutorial
lake build
rm -rf html _out
lake exe manual
mkdir html
mv _out/html-multi/* html/
rm -rf _out
mkdir -p html/static
cp static_files/* html/static
cd ..

# Copy outputs to home_page
mkdir -p home_page/tutorial
cp -r tutorial/html/* home_page/tutorial
