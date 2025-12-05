const std = @import("std");
const zirb = @import("RedBlackTree.zig");

// Define the data structure that embeds the tree node.
const MyDataNode = struct {
    id: u32,
    name: []const u8,
    node: zirb.Node,
};

// Helper to get the containing MyDataNode from a tree node.
fn getNodeData(n: *const zirb.Node) *const MyDataNode {
    return @fieldParentPtr("node", n);
}

// Comparison function for inserting nodes.
fn compareNodes(context: void, lhs: *const zirb.Node, rhs: *const zirb.Node) std.math.Order {
    _ = context;
    const lhs_data = getNodeData(lhs);
    const rhs_data = getNodeData(rhs);
    return std.math.order(lhs_data.id, rhs_data.id);
}

// Comparison function for searching by key.
fn compareKeyToNode(context: void, key: comptime_int, node: *const zirb.Node) std.math.Order {
    _ = context;
    const node_data = getNodeData(node);
    return std.math.order(key, node_data.id);
}

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const allocator = gpa.allocator();

    // Initialize the tree.
    var tree = zirb.RedBlackTree{};

    // Create and insert nodes.
    const data_to_insert = [_]struct {
        id: u32,
        name: []const u8,
    }{
        .{ .id = 10, .name = "ten" },
        .{ .id = 5, .name = "five" },
        .{ .id = 15, .name = "fifteen" },
        .{ .id = 1, .name = "one" },
        .{ .id = 7, .name = "seven" },
    };

    var nodes = std.ArrayList(MyDataNode).empty;
    try nodes.ensureTotalCapacity(allocator, data_to_insert.len);
    defer nodes.deinit(allocator);

    std.debug.print("Inserting nodes...\n", .{});
    for (data_to_insert, 0..) |data, i| {
        nodes.appendAssumeCapacity(.{
            .id = data.id,
            .name = data.name,
            .node = .{},
        });
        tree.insert(&nodes.items[i].node, {}, compareNodes);
        std.debug.print("\tInserted: id = {d}, name = {s}\n", .{ data.id, data.name });
    }

    // Iterate over the tree in order and print the data.
    std.debug.print("\nIn-order traversal:\n", .{});
    var it = tree.inorder();
    while (it.next()) |node_ptr| {
        const data_node = getNodeData(node_ptr);
        std.debug.print("\tid = {d}, name = {s}\n", .{ data_node.id, data_node.name });
    }

    // Find and remove a node.
    std.debug.print("\nRemoving node with id = 10...\n", .{});
    const node_to_remove = tree.search(10, {}, compareKeyToNode) orelse {
        std.debug.print("Node not found!\n", .{});
        return;
    };
    tree.remove(node_to_remove);

    // Iterate again to show the node has been removed.
    std.debug.print("\nIn-order traversal after removal:\n", .{});
    var it_after_remove = tree.inorder();
    while (it_after_remove.next()) |node_ptr| {
        const data_node = getNodeData(node_ptr);
        std.debug.print("\tid = {d}, name = {s}\n", .{ data_node.id, data_node.name });
    }
}
