//! This file provides a generic, intrusive Red-Black Tree implementation. It is designed to be
//! flexible, allowing users to define the key type, a context for comparisons, and the comparison
//! function itself at compile time.
//!
//! Being intrusive means the tree does not own the memory for its nodes. The caller is responsible
//! for allocating and deallocating `Node` objects. This is useful for high-performance scenarios or
//! when nodes are part of a larger, existing struct.

// Copyright 2025 Pascal Zittlau
//
// Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
// associated documentation files (the “Software”), to deal in the Software without restriction,
// including without limitation the rights to use, copy, modify, merge, publish, distribute,
// sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in all copies or
// substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
// NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
// DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

const std = @import("std");
const testing = std.testing;
const assert = std.debug.assert;

/// A utility to create a packed pointer that combines a pointer and a small integer tag. In this
/// case, it's used to store the parent pointer and the node's color in a single `usize`. This is
/// a space optimization that leverages pointer alignment to store extra data in the unused
/// low-order bits of the pointer.
fn TaggedPackedPtr(
    comptime Pointer: type,
    comptime Tag: type,
) type {
    return packed struct(usize) {
        comptime {
            const tag_bits = @bitSizeOf(Tag);
            const required_alignment = 1 << tag_bits;
            if (@alignOf(Pointer) < required_alignment) {
                @compileError("Pointer type is not aligned enough to store the tag bits.");
            }
        }

        const PointerSize = ptr: {
            var info = @typeInfo(usize);
            info.int.bits -= @bitSizeOf(Tag);
            break :ptr @Type(info);
        };

        tag: Tag,
        ptr: PointerSize,

        fn init(ptr: ?*Pointer, tag: Tag) @This() {
            return @This(){ .tag = tag, .ptr = @intCast(@intFromPtr(ptr) >> @bitSizeOf(Tag)) };
        }

        fn get(self: @This()) ?*Pointer {
            return @ptrFromInt(@as(usize, self.ptr) << @bitSizeOf(Tag));
        }

        fn set(self: *@This(), ptr: ?*Pointer) void {
            self.ptr = @intCast(@intFromPtr(ptr) >> @bitSizeOf(Tag));
        }
    };
}

/// Represents the color of a Red-Black Tree node, used for balancing.
const Color = enum(u1) {
    red = 0,
    black = 1,
};

/// A generic, intrusive Red-Black Tree implementation.
///
/// This function returns a struct type that represents the tree. Being intrusive means the tree
/// does not own the memory for its nodes. The caller is responsible for allocating and deallocating
/// `Node` objects. This is useful for high-performance scenarios or when nodes are part of
/// a larger, existing struct.
///
/// Parameters:
///   - `K`: The type of the key/payload stored in each node.
///   - `Context`: A context type passed to the comparison function or `void` if not needed.
///   - `compareFn`: A comptime-known function pointer used to compare two keys.
///     It must return `std.math.Order.lt` if the first key is less than the second,
///     `.gt` if greater, and `.eq` if equal.
pub fn RedBlackTree(
    comptime K: type,
    comptime Context: type,
    comptime compareFn: fn (context: Context, lhs: K, rhs: K) std.math.Order,
) type {
    return struct {
        const Self = @This();
        root: ?*Node = null,
        context: Context = undefined,

        /// Represents a single node in the Red-Black Tree.
        /// Users of the tree must allocate nodes of this type.
        pub const Node = struct {
            /// The user-defined data stored in this node.
            payload: K,
            parent: TaggedPackedPtr(Node, Color) = .init(null, .red),
            left: ?*Node = null,
            right: ?*Node = null,

            /// Sets the parent pointer of this node.
            fn setParent(self: *Node, p: ?*Node) void {
                self.parent.set(p);
            }

            /// Gets the parent pointer of this node.
            fn getParent(self: *const Node) ?*Node {
                return self.parent.get();
            }

            /// Gets the color of this node.
            fn getColor(self: *const Node) Color {
                return self.parent.tag;
            }

            /// Sets the color of this node.
            fn setColor(self: *Node, color: Color) void {
                self.parent.tag = color;
            }

            /// Copies the color from another node to this node.
            fn copyColor(dest: *Node, src: *const Node) void {
                dest.setColor(src.getColor());
            }

            /// Finds the node with the minimum value in the subtree rooted at `self`.
            pub fn minimum(self: *Node) *Node {
                var node = self;
                while (node.left) |l| {
                    node = l;
                }
                return node;
            }

            /// Finds the node with the maximum value in the subtree rooted at `self`.
            pub fn maximum(self: *Node) *Node {
                var node = self;
                while (node.right) |r| {
                    node = r;
                }
                return node;
            }

            /// Returns the inorder successor of this node.
            /// If this node has a right child, the successor is the minimum node in the right
            /// subtree. Otherwise, it's the lowest ancestor of this node whose left child is also
            /// an ancestor of this node.
            pub fn next(self: *Node) ?*Node {
                if (self.right) |r| {
                    return r.minimum();
                }
                var current: ?*Node = self;
                var p = current.?.getParent();
                while (p != null and current == p.?.right) {
                    current = p;
                    p = current.?.getParent();
                }
                assert(p == null or current == p.?.left);
                return p;
            }

            /// Returns the inorder predecessor of this node.
            /// If this node has a left child, the predecessor is the maximum node in the left
            /// subtree. Otherwise, it's the lowest ancestor of this node whose right child is also
            /// an ancestor of this node.
            pub fn prev(self: *Node) ?*Node {
                if (self.left) |l| {
                    return l.maximum();
                }
                var current: ?*Node = self;
                var p = current.?.getParent();
                while (p != null and current == p.?.left) {
                    current = p;
                    p = current.?.getParent();
                }
                assert(p == null or current == p.?.right);
                return p;
            }

            /// Checks if this node is a child of the `other` node.
            fn isChildOf(self: *const Node, other: *const Node) bool {
                return self == other.left or self == other.right;
            }
        };

        /// A range of nodes, defined by a start (inclusive) and end (exclusive) node pointer.
        pub const Range = struct { start: ?*Node, end: ?*Node };

        /// Checks if a node is black. Null nodes are considered black.
        fn isBlack(node: ?*const Node) bool {
            // Leaf (null) nodes are considered black.
            return node == null or node.?.parent.tag == .black;
        }

        /// Checks if a node is red.
        fn isRed(node: ?*const Node) bool {
            return !isBlack(node);
        }

        /// Returns `true` if the tree contains no nodes.
        pub fn isEmpty(tree: *const Self) bool {
            return tree.root == null;
        }

        /// Replaces node `u` with node `v` in the tree structure.
        /// This is a core helper for rotations and removal. It updates parent pointers to reflect
        /// the change in tree structure.
        fn splice(tree: *Self, u: *Node, v: ?*Node) void {
            const p = u.getParent();
            if (p) |p_node| {
                if (u == p_node.left) {
                    p_node.left = v;
                } else {
                    assert(u == p_node.right);
                    p_node.right = v;
                }
            } else {
                assert(tree.root == u);
                tree.root = v;
            }
            if (v) |v_node| {
                v_node.setParent(p);
            }
        }

        /// Performs a left rotation on the subtree rooted at `x`.
        /// This operation rearranges nodes to maintain Red-Black Tree properties.
        /// `x` must have a right child.
        fn rotateLeft(tree: *Self, x: *Node) void {
            const y = x.right orelse @panic("rotateLeft requires a right child.");
            x.right = y.left;
            if (y.left) |y_left| {
                y_left.setParent(x);
            }
            tree.splice(x, y);
            y.left = x;
            x.setParent(y);
        }

        /// Performs a right rotation on the subtree rooted at `y`.
        /// This operation rearranges nodes to maintain Red-Black Tree properties.
        /// `y` must have a left child.
        fn rotateRight(tree: *Self, y: *Node) void {
            const x = y.left orelse @panic("rotateRight requires a left child.");
            y.left = x.right;
            if (x.right) |x_right| {
                x_right.setParent(y);
            }
            tree.splice(y, x);
            x.right = y;
            y.setParent(x);
        }

        /// Inserts a `node` into the tree.
        ///
        /// The tree is rebalanced after insertion to maintain the Red-Black properties. If a node
        /// with an equal key already exists, the new node is inserted as its successor, allowing
        /// for duplicate keys (multiset behavior).
        ///
        /// Parameters:
        ///   - `tree`: A pointer to the Red-Black Tree instance.
        ///   - `node`: A pointer to the `Node` to be inserted. This node must be allocated by the caller.
        pub fn insert(
            tree: *Self,
            node: *Node,
        ) void {
            var parent: ?*Node = null;
            var x = tree.root;
            var left = false;
            while (x) |x_node| {
                parent = x;
                switch (compareFn(tree.context, node.payload, x_node.payload)) {
                    .lt => {
                        x = x_node.left;
                        left = true;
                    },
                    .gt, .eq => {
                        x = x_node.right;
                        left = false;
                    },
                }
            }
            tree.insertAt(parent, node, left);
        }

        /// Inserts a node at a pre-determined position and then rebalances the tree.
        /// This function handles the Red-Black Tree insertion fix-up cases.
        pub fn insertAt(tree: *Self, parent: ?*Node, node: *Node, insert_left: bool) void {
            node.*.left = null;
            node.*.right = null;
            node.*.parent = .init(null, .red); // New node is always red

            if (parent) |p| {
                if (insert_left) {
                    assert(p.left == null);
                    p.left = node;
                } else {
                    assert(p.right == null);
                    p.right = node;
                }
            } else {
                // Insert root.
                assert(tree.root == null);
                tree.root = node;
                node.setColor(.black); // Root is always black
                return;
            }
            node.setParent(parent);

            var z = node; // z is the newly inserted node
            while (isRed(z.getParent())) { // While parent of z is red (violates property 4)
                var p: *Node = z.getParent().?; // p is parent of z
                assert(z.isChildOf(p));
                var gp: *Node = p.getParent().?; // gp is grandparent of z
                assert(p.isChildOf(gp));
                if (p == gp.left) { // Case 1: Parent is a left child of grandparent
                    const uncle = gp.right; // Uncle is right child of grandparent
                    if (isRed(uncle)) {
                        // Case 1 (recolor): Parent, uncle, and grandparent are involved.
                        // Recolor parent and uncle to black, grandparent to red.
                        // Move z up to grandparent and repeat.
                        p.setColor(.black);
                        uncle.?.setColor(.black);
                        gp.setColor(.red);
                        z = gp;
                    } else {
                        // Case 2 (rotate): Uncle is black.
                        // If z is a right child, rotate left on parent to transform to Case 3.
                        if (z == p.right) {
                            z = p;
                            tree.rotateLeft(z);
                            p = z.getParent().?; // Update p after rotation
                            assert(z.isChildOf(p));
                            gp = p.getParent().?; // Update gp after rotation
                        }
                        // Case 3 (recolor and rotate): Uncle is black, z is a left child.
                        // Recolor parent to black, grandparent to red. Rotate right on grandparent.
                        p.setColor(.black);
                        gp.setColor(.red);
                        tree.rotateRight(gp);
                    }
                } else { // p == gp.right (Symmetric cases for parent being a right child)
                    const uncle = gp.left; // Uncle is left child of grandparent
                    if (isRed(uncle)) {
                        // Case 1 (recolor): Symmetric to above.
                        p.setColor(.black);
                        uncle.?.setColor(.black);
                        gp.setColor(.red);
                        z = gp;
                    } else {
                        // Case 2 (rotate): Symmetric to above.
                        // If z is a left child, rotate right on parent to transform to Case 3.
                        if (z == p.left) {
                            z = p;
                            tree.rotateRight(z);
                            p = z.getParent().?; // Update p after rotation
                            assert(z.isChildOf(p));
                            gp = p.getParent().?; // Update gp after rotation
                        }
                        // Case 3 (recolor and rotate): Symmetric to above.
                        // Recolor parent to black, grandparent to red. Rotate left on grandparent.
                        p.setColor(.black);
                        gp.setColor(.red);
                        tree.rotateLeft(gp);
                    }
                }
            }
            tree.root.?.setColor(.black); // Ensure root is always black (property 2)
        }

        /// Removes a `node` from the tree.
        ///
        /// The caller must provide a pointer to the exact `Node` to be removed.
        /// The tree is rebalanced after removal to maintain the Red-Black properties.
        /// The memory for the node is not freed.
        ///
        /// Parameters:
        ///   - `tree`: A pointer to the Red-Black Tree instance.
        ///   - `z`: A pointer to the `Node` to be removed.
        pub fn remove(tree: *Self, z: *Node) void {
            var x: ?*Node = null; // x is the node that replaces y in the tree
            var x_p: ?*Node = null; // x_p is the parent of x
            var y = z; // y is the node that is actually removed or moved
            var y_was_black = y.getColor() == .black; // Store original color of y

            if (z.left == null) { // Case 1: z has no left child
                x = z.right;
                x_p = z.getParent();
                tree.splice(z, x);
            } else if (z.right == null) { // Case 2: z has no right child
                x = z.left;
                x_p = z.getParent();
                tree.splice(z, x);
            } else { // Case 3: z has two children
                y = z.right.?.minimum(); // y is z's successor
                y_was_black = y.getColor() == .black;
                x = y.right;

                if (y.getParent() == z) { // If y is a direct child of z
                    x_p = y;
                } else { // y is not a direct child of z
                    x_p = y.getParent();
                    tree.splice(y, x); // Remove y from its current position
                    y.right = z.right;
                    y.right.?.setParent(y);
                }
                assert(y.left == null); // Successor should not have a left child
                tree.splice(z, y); // Replace z with y
                y.left = z.left;
                y.left.?.setParent(y);
                y.copyColor(z); // y inherits z's color
            }

            assert(x_p == null or x == null or x.?.isChildOf(x_p.?));

            if (!y_was_black) return; // If y was red, no Red-Black properties are violated.

            // Fixup after delete (if y was black, we need to rebalance)
            var x_mut = x;
            var x_p_mut = x_p;
            while (x_mut != tree.root and isBlack(x_mut)) {
                const current_x_p = x_p_mut orelse x_mut.?.getParent() orelse break;

                if (x_mut == current_x_p.left) { // x is a left child
                    var w = current_x_p.right; // w is x's sibling
                    if (isRed(w)) { // Case 1: Sibling w is red
                        w.?.setColor(.black);
                        current_x_p.setColor(.red);
                        tree.rotateLeft(current_x_p);
                        w = current_x_p.right; // Update w after rotation
                    }

                    const w_node = w orelse break;
                    if (isBlack(w_node.left) and isBlack(w_node.right)) {
                        // Case 2: Sibling w is black, and both of w's children are black
                        w_node.setColor(.red);
                        x_mut = current_x_p; // Move x up to its parent
                        x_p_mut = x_mut.?.getParent();
                    } else {
                        if (isBlack(w_node.right)) {
                            // Case 3: Sibling w is black, w's left child is red, w's right child is black
                            if (w_node.left) |wl| wl.setColor(.black);
                            w_node.setColor(.red);
                            tree.rotateRight(w_node);
                            w = current_x_p.right; // Update w after rotation
                        }
                        // Case 4: Sibling w is black, w's right child is red
                        const new_w_node = w orelse break;
                        new_w_node.copyColor(current_x_p);
                        current_x_p.setColor(.black);
                        if (new_w_node.right) |r| r.setColor(.black);
                        tree.rotateLeft(current_x_p);
                        x_mut = tree.root; // Done, set x to root to terminate loop
                        x_p_mut = null;
                    }
                } else { // symmetric case: x == x_p.right (x is a right child)
                    var w = current_x_p.left; // w is x's sibling
                    if (isRed(w)) { // Case 1: Sibling w is red (symmetric)
                        w.?.setColor(.black);
                        current_x_p.setColor(.red);
                        tree.rotateRight(current_x_p);
                        w = current_x_p.left; // Update w after rotation
                    }

                    const w_node = w orelse break;
                    if (isBlack(w_node.right) and isBlack(w_node.left)) {
                        // Case 2: Sibling w is black, and both of w's children are black (symmetric)
                        w_node.setColor(.red);
                        x_mut = current_x_p; // Move x up to its parent
                        x_p_mut = x_mut.?.getParent();
                    } else {
                        if (isBlack(w_node.left)) {
                            // Case 3: Sibling w is black, w's right child is red, w's left child is black (symmetric)
                            if (w_node.right) |wr| wr.setColor(.black);
                            w_node.setColor(.red);
                            tree.rotateLeft(w_node);
                            w = current_x_p.left; // Update w after rotation
                        }
                        // Case 4: Sibling w is black, w's left child is red (symmetric)
                        const new_w_node = w orelse break;
                        new_w_node.copyColor(current_x_p);
                        current_x_p.setColor(.black);
                        if (new_w_node.left) |l| l.setColor(.black);
                        tree.rotateRight(current_x_p);
                        x_mut = tree.root; // Done, set x to root to terminate loop
                        x_p_mut = null;
                    }
                }
            }

            if (x_mut) |node| {
                node.setColor(.black); // Ensure the final node (x) is black
            }
        }

        /// Searches for a node with a matching key, removes it from the tree, and returns it.
        /// Returns null if no matching node was found. The caller is responsible for deallocating
        /// the returned node.
        ///
        /// Parameters:
        ///   - `tree`: A pointer to the Red-Black Tree instance.
        ///   - `key`: The key of the node to find and remove.
        pub fn findAndRemove(tree: *Self, key: K) ?*Node {
            const node_to_remove = tree.search(key) orelse return null;
            tree.remove(node_to_remove);
            return node_to_remove;
        }

        /// Returns the first (left-most) node in the tree, which has the smallest key.
        /// Returns `null` if the tree is empty.
        pub fn first(tree: *const Self) ?*Node {
            return if (tree.root) |r| r.minimum() else null;
        }

        /// Returns the last (right-most) node in the tree, which has the largest key.
        /// Returns `null` if the tree is empty.
        pub fn last(self: *const Self) ?*Node {
            return if (self.root) |r| r.maximum() else null;
        }

        /// Searches for a node with a key equal to `key`.
        ///
        /// Returns a pointer to the first node found that matches `key`, or `null` if no such node
        /// exists. If multiple nodes have the same key, which one is returned is not specified.
        ///
        /// Parameters:
        ///   - `tree`: A pointer to the Red-Black Tree instance.
        ///   - `key`: The key to search for.
        pub fn search(tree: *const Self, key: K) ?*Node {
            var x = tree.root;
            while (x) |x_node| {
                switch (compareFn(tree.context, key, x_node.payload)) {
                    .lt => x = x_node.left,
                    .gt => x = x_node.right,
                    .eq => return x_node,
                }
            }
            return null;
        }

        /// Checks if the tree contains a node with a key equal to `key`.
        ///
        /// Parameters:
        ///   - `tree`: A pointer to the Red-Black Tree instance.
        ///   - `key`: The key to check for existence.
        pub fn contains(tree: *const Self, key: K) bool {
            return tree.search(key) != null;
        }

        /// Searches for a key. If an exact match is found, it's returned.
        /// Otherwise, returns the node that would be the parent of the key if it were to be
        /// inserted. This can be useful for manual insertion placement. Returns `null` if the tree
        /// is empty.
        ///
        /// Parameters:
        ///   - `tree`: A pointer to the Red-Black Tree instance.
        ///   - `key`: The key to search for or find an insertion point for.
        pub fn findInsertionPoint(tree: *const Self, key: K) ?*Node {
            var parent: ?*Node = null;
            var x = tree.root;
            while (x) |x_node| {
                parent = x_node;
                switch (compareFn(tree.context, key, x_node.payload)) {
                    .lt => x = x_node.left,
                    .gt => x = x_node.right,
                    .eq => return x_node,
                }
            }
            return parent;
        }

        /// Finds the first node in the tree whose key is greater than or equal to `key`.
        /// Returns `null` if no such node exists.
        ///
        /// Parameters:
        ///   - `tree`: A pointer to the Red-Black Tree instance.
        ///   - `key`: The key to search for.
        pub fn lowerBound(tree: *const Self, key: K) ?*Node {
            var result: ?*Node = null;
            var current = tree.root;
            while (current) |node| {
                switch (compareFn(tree.context, node.payload, key)) {
                    .lt => current = node.right,
                    .eq, .gt => {
                        result = node;
                        current = node.left;
                    },
                }
            }
            return result;
        }

        /// Finds the first node in the tree whose key is strictly greater than `key`.
        /// Returns `null` if no such node exists.
        ///
        /// Parameters:
        ///   - `tree`: A pointer to the Red-Black Tree instance.
        ///   - `key`: The key to search for.
        pub fn upperBound(tree: *const Self, key: K) ?*Node {
            var result: ?*Node = null;
            var current = tree.root;
            while (current) |node| {
                switch (compareFn(tree.context, key, node.payload)) {
                    .lt => {
                        result = node;
                        current = node.left;
                    },
                    .eq, .gt => current = node.right,
                }
            }
            return result;
        }

        /// Returns a `Range` of all nodes whose keys are equal to `key`.
        /// The range is `[start, end)`, where `start` is the first node with the key (inclusive)
        /// and `end` is the first node with a key greater than `key` (exclusive).
        /// If no nodes match `key`, `start` and `end` will be equal.
        ///
        /// Parameters:
        ///   - `tree`: A pointer to the Red-Black Tree instance.
        ///   - `key`: The key to find the range for.
        pub fn equalRange(tree: *const Self, key: K) Range {
            return .{
                .start = tree.lowerBound(key),
                .end = tree.upperBound(key),
            };
        }

        /// An iterator for traversing the tree in ascending order of keys (in-order).
        pub const InorderIterator = struct {
            node: ?*Node,

            /// Returns the next node in the in-order traversal, or `null` if the iteration is complete.
            pub fn next(self: *InorderIterator) ?*Node {
                if (self.node) |n| {
                    self.node = n.next();
                    return n;
                } else {
                    return null;
                }
            }
        };

        /// Returns an iterator that traverses nodes from first (smallest key) to last (largest key).
        pub fn inorder(tree: *const Self) InorderIterator {
            return .{ .node = tree.first() };
        }

        /// An iterator for traversing the tree in descending order of keys (reverse in-order).
        pub const ReverseInorderIterator = struct {
            node: ?*Node,

            /// Returns the next node in the reverse in-order traversal, or `null` if the iteration
            /// is complete.
            pub fn next(self: *ReverseInorderIterator) ?*Node {
                if (self.node) |n| {
                    self.node = n.prev();
                    return n;
                } else {
                    return null;
                }
            }
        };

        /// Returns an iterator that traverses nodes from last (largest key) to first (smallest key).
        pub fn reverseInorder(tree: *const Self) ReverseInorderIterator {
            return .{ .node = tree.last() };
        }

        /// An iterator for traversing the tree in pre-order (Root, Left, Right).
        pub const PreorderIterator = struct {
            node: ?*Node,

            /// Returns the next node in the pre-order traversal, or `null` if the iteration is complete.
            pub fn next(self: *PreorderIterator) ?*Node {
                const current = self.node orelse return null;

                // Determine the next node
                if (current.left) |next_node| {
                    self.node = next_node;
                } else if (current.right) |next_node| {
                    self.node = next_node;
                } else {
                    // Go up until we find a parent with an unvisited right branch
                    var temp = current;
                    while (temp.getParent()) |p| {
                        // If we came from the left and there is a right child, go there.
                        if (temp == p.left and p.right != null) {
                            self.node = p.right;
                            return current;
                        }
                        // Otherwise, continue up.
                        temp = p;
                    }
                    // If we reach the root and have gone up, we are done.
                    self.node = null;
                }

                return current;
            }
        };

        /// Returns an iterator that traverses nodes in pre-order (Root, Left, Right).
        pub fn preorder(tree: *const Self) PreorderIterator {
            return .{ .node = tree.root };
        }

        /// An iterator for traversing the tree in post-order (Left, Right, Root).
        pub const PostorderIterator = struct {
            node: ?*Node,

            /// Returns the next node in the post-order traversal, or `null` if the iteration is complete.
            pub fn next(self: *PostorderIterator) ?*Node {
                const current = self.node orelse return null;

                const parent = current.getParent();
                if (parent == null) {
                    // We just returned the root, so we are done.
                    self.node = null;
                    return current;
                }

                // If we were the left child and a right sibling exists,
                // the next node is the minimum of the right subtree.
                if (current == parent.?.left and parent.?.right != null) {
                    self.node = parent.?.right.?.minimum();
                } else {
                    // Otherwise, we've finished with the children of the parent,
                    // so the next node to visit is the parent itself.
                    self.node = parent;
                }

                return current;
            }
        };

        /// Returns an iterator that traverses nodes in post-order (Left, Right, Root).
        pub fn postorder(tree: *const Self) PostorderIterator {
            return .{ .node = if (tree.root) |r| r.minimum() else null };
        }
    };
}

const TestInt = u32;
const TestTree = RedBlackTree(TestInt, void, testCompare);
fn testCompare(_: void, lhs: TestInt, rhs: TestInt) std.math.Order {
    return std.math.order(lhs, rhs);
}
const TestNode = TestTree.Node;

test "insert, search, inorder, remove" {
    var tree = TestTree{};
    try std.testing.expect(tree.isEmpty());
    const count = 1000;

    var reference = try std.ArrayListUnmanaged(TestNode).initCapacity(std.testing.allocator, count);
    defer reference.deinit(std.testing.allocator);
    var prng = std.Random.DefaultPrng.init(42);
    const r = prng.random();

    for (0..count) |_| {
        const val = r.int(TestInt);
        const item = TestNode{ .payload = val };
        reference.appendAssumeCapacity(item);
    }

    var timer = try std.time.Timer.start();
    for (0..count) |i| {
        const item = &reference.items[i];
        std.log.debug("Inserting: {}", .{item.payload});
        tree.insert(item);

        var iter = tree.inorder();
        var j: u64 = 0;
        var prev: TestInt = 0;
        while (iter.next()) |n| : (j += 1) {
            std.log.debug("{} ", .{n.payload});
            if (j > 0) {
                try std.testing.expect(prev <= n.payload);
            }
            prev = n.payload;
        }
        std.log.debug("", .{});
        try std.testing.expectEqual(i + 1, j);
    }
    try std.testing.expect(!tree.isEmpty());
    std.log.info("Insertion took {}us", .{timer.lap() / std.time.ns_per_us});

    for (0..count) |i| {
        const index = count - i - 1; // reverse
        const item = &reference.items[index];
        const node_opt = tree.search(item.payload);
        try std.testing.expect(node_opt != null);
        tree.remove(node_opt.?);

        var iter = tree.inorder();
        var j: u64 = 0;
        var prev: TestInt = 0;
        while (iter.next()) |n| : (j += 1) {
            std.log.debug("{} ", .{n.payload});
            if (j > 0) {
                try std.testing.expect(prev <= n.payload);
            }
            prev = n.payload;
        }
        std.log.debug("", .{});
        try std.testing.expectEqual(index, j);
    }
    try std.testing.expect(tree.isEmpty());
    std.log.info("Removal took {}us", .{timer.lap() / std.time.ns_per_us});
}

// A helper struct to set up a standard tree for testing boundary functions.
const TestSetup = struct {
    tree: TestTree,
    nodes: std.ArrayListUnmanaged(TestNode),
    sorted_data: std.ArrayListUnmanaged(TestInt),

    fn init() !TestSetup {
        var self = TestSetup{
            .tree = TestTree{ .context = {} },
            .nodes = .empty,
            .sorted_data = .empty,
        };

        const data = [_]TestInt{ 30, 20, 50, 10, 60, 40, 20, 50, 50 };
        errdefer self.deinit();
        for (data) |payload| {
            try self.nodes.append(std.testing.allocator, .{ .payload = payload });
        }
        for (self.nodes.items) |*node| {
            self.tree.insert(node);
        }

        self.sorted_data = .fromOwnedSlice(try std.testing.allocator.dupe(TestInt, &data));
        std.mem.sortUnstable(TestInt, self.sorted_data.items, {}, struct {
            fn inner(_: void, lhs: TestInt, rhs: TestInt) bool {
                return lhs < rhs;
            }
        }.inner);

        return self;
    }

    fn min(self: *const TestSetup) TestInt {
        return self.sorted_data.items[0];
    }

    fn max(self: *const TestSetup) TestInt {
        return self.sorted_data.getLast();
    }

    fn deinit(self: *TestSetup) void {
        self.nodes.deinit(std.testing.allocator);
        self.sorted_data.deinit(std.testing.allocator);
    }
};

test "first and last" {
    var setup = try TestSetup.init();
    defer setup.deinit();

    try testing.expectEqual(setup.min(), setup.tree.first().?.payload);
    try testing.expectEqual(setup.max(), setup.tree.last().?.payload);
}

test "inorder iterator" {
    var setup = try TestSetup.init();
    defer setup.deinit();

    var inorder_it = setup.tree.inorder();
    var last: ?TestInt = null;
    for (setup.sorted_data.items) |expected| {
        const node = inorder_it.next() orelse {
            return error.TestExpectedEqual;
        };
        if (last) |l| {
            try testing.expect(l <= node.payload);
        }
        last = node.payload;
        try testing.expectEqual(expected, node.payload);
    }
    try testing.expectEqual(null, inorder_it.next()); // Ensure it's finished
}

test "reverseInorder iterator" {
    var setup = try TestSetup.init();
    defer setup.deinit();

    var reverse_it = setup.tree.reverseInorder();
    var last: ?TestInt = null;
    for (setup.sorted_data.items, 0..) |_, i| {
        const expected_rev = setup.sorted_data.items[setup.sorted_data.items.len - 1 - i];
        const node = reverse_it.next() orelse {
            return error.TestExpectedEqual;
        };
        if (last) |l| {
            try testing.expect(l >= node.payload);
        }
        last = node.payload;
        try testing.expectEqual(expected_rev, node.payload);
    }
    try testing.expectEqual(null, reverse_it.next()); // Ensure it's finished
}

test "lowerBound" {
    var setup = try TestSetup.init();
    defer setup.deinit();

    // Exact match
    try testing.expectEqual(30, setup.tree.lowerBound(30).?.payload);
    // In-between value
    try testing.expectEqual(40, setup.tree.lowerBound(35).?.payload);
    // Value smaller than all elements
    try testing.expectEqual(setup.min(), setup.tree.lowerBound(setup.min() - 1).?.payload);
    // Value larger than all elements
    try testing.expectEqual(null, setup.tree.lowerBound(setup.max() + 1));
    // Duplicates (should find first `20`)
    const first_20 = setup.tree.lowerBound(20).?;
    try testing.expectEqual(20, first_20.payload);
    try testing.expectEqual(10, first_20.prev().?.payload);
}

test "upperBound" {
    var setup = try TestSetup.init();
    defer setup.deinit();

    try testing.expectEqual(40, setup.tree.upperBound(30).?.payload);
    // Duplicates (should find node after all `50`s)
    try testing.expectEqual(60, setup.tree.upperBound(50).?.payload);
    // Last element
    try testing.expectEqual(null, setup.tree.upperBound(setup.max()));
    // Value smaller than all elements
    try testing.expectEqual(setup.min(), setup.tree.upperBound(setup.min() - 1).?.payload);
}

test "equalRange" {
    var setup = try TestSetup.init();
    defer setup.deinit();

    // Non-existent key
    const range_25 = setup.tree.equalRange(25);
    try testing.expect(range_25.start == range_25.end);

    // Unique key
    const range_30 = setup.tree.equalRange(30);
    try testing.expectEqual(30, range_30.start.?.payload);
    try testing.expect(range_30.start.?.next() == range_30.end);

    // Multiple keys (50 appears 3 times)
    const range_50 = setup.tree.equalRange(50);
    var current = range_50.start;
    var count: u32 = 0;
    while (current != range_50.end) : (count += 1) {
        try testing.expectEqual(50, current.?.payload);
        current = current.?.next();
    }
    try testing.expectEqual(3, count);
    try testing.expectEqual(60, range_50.end.?.payload);
}

test "preorder iterator" {
    var setup = try TestSetup.init();
    defer setup.deinit();

    // The expected preorder traversal for the tree created in TestSetup.
    // (Root, Left, Right)
    const expected_preorder = [_]TestInt{ 30, 20, 10, 20, 50, 40, 50, 50, 60 };

    var it = setup.tree.preorder();
    for (expected_preorder) |expected_val| {
        const node = it.next() orelse {
            return error.TestExpectedEqual;
        };
        try testing.expectEqual(expected_val, node.payload);
    }

    // Ensure the iterator is fully consumed.
    try testing.expectEqual(null, it.next());
}

test "postorder iterator" {
    var setup = try TestSetup.init();
    defer setup.deinit();

    // The expected postorder traversal for the tree created in TestSetup.
    // (Left, Right, Root)
    const expected_postorder = [_]TestInt{ 10, 20, 20, 40, 50, 60, 50, 50, 30 };

    var it = setup.tree.postorder();
    for (expected_postorder) |expected_val| {
        const node = it.next() orelse {
            return error.TestExpectedEqual;
        };
        try testing.expectEqual(expected_val, node.payload);
    }

    // Ensure the iterator is fully consumed.
    try testing.expectEqual(null, it.next());
}
