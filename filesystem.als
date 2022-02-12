// signatures

abstract sig FSObject { }
sig File, Dir extends FSObject { }

sig FileSystem {
	live: set FSObject,
	root: Dir & live,
	contents: Dir -> FSObject,
	parent: (live - root) ->one (Dir & live)
}{
	live = root.*contents
	parent = ~contents
}

pred move [fs, fs2: FileSystem, x: FSObject, d: Dir] {
  (x + d) in fs.live
  fs2.parent = fs.parent - x->(x.(fs.parent)) + x->d
}

moveOkay: check {
	all fs, fs2: FileSystem, x: FSObject, d: Dir |
		move[fs, fs2, x, d] => fs2.live = fs.live
} for 5

pred remove [fs, fs2: FileSystem, x: FSObject] {
	x in (fs.live - fs.root)
	fs.root = fs2.root
	fs2.parent = fs.parent - x->(x.(fs.parent))
}

pred removeAll [fs, fs2: FileSystem, x: FSObject] {
	x in (fs.live - fs.root)
	fs.root = fs2.root
	let subtree = x.*(fs.contents) |
		fs2.parent = fs.parent - subtree->(subtree.*(fs.parent))
}

removeOkay: check {
	all fs, fs2: FileSystem, x: FSObject |
		remove[fs, fs2, x] => fs2.live = fs.live -x
} for 5

removeAllOkay: check {
	all fs, fs2: FileSystem, d: Dir |
		removeAll[fs, fs2, d] => fs2.live = fs.live - d.*(fs.contents)
} for 5

removeAllSame: check {
	all fs, fs1, fs2: FileSystem, f: File |
		remove[fs, fs1, f] && removeAll[fs, fs2, f] => fs1.live = fs2.live

run move for 2 FileSystem, 4 FSObject
