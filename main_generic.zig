const std = @import("std");
const zirb = @import("generic_red_black_tree.zig");

// Define the data structure to be stored in the tree.
const MyData = struct {
    id: u32,
    name: []const u8,
};

// Define the comparison function for MyData.
fn compareMyData(context: void, lhs: MyData, rhs: MyData) std.math.Order {
    _ = context;
    return std.math.order(lhs.id, rhs.id);
}

// Define the tree type using the generic RedBlackTree.
const MyTree = zirb.RedBlackTree(MyData, void, compareMyData);

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const allocator = gpa.allocator();

    // Initialize the tree.
    var tree = MyTree{ .context = {} };

    // Create and insert nodes.
    const data_to_insert = [_]MyData{
        .{ .id = 10, .name = "ten" },
        .{ .id = 5, .name = "five" },
        .{ .id = 15, .name = "fifteen" },
        .{ .id = 1, .name = "one" },
        .{ .id = 7, .name = "seven" },
    };

    var nodes = std.ArrayList(*MyTree.Node).init(allocator);
    defer {
        for (nodes.items) |node| {
            allocator.destroy(node);
        }
        nodes.deinit();
    }

    std.debug.print("Inserting nodes...\n", .{});
    for (data_to_insert) |data| {
        const node = try allocator.create(MyTree.Node);
        node.* = .{ .payload = data };
        try nodes.append(node);
        tree.insert(node);
        std.debug.print("\tInserted: id = {d}, name = {s}\n", .{ data.id, data.name });
    }

    // Iterate over the tree in order and print the data.
    std.debug.print("\nIn-order traversal:\n", .{});
    var it = tree.inorder();
    while (it.next()) |node| {
        std.debug.print("\tid = {d}, name = {s}\n", .{ node.payload.id, node.payload.name });
    }

    // Find and remove a node.
    std.debug.print("\nRemoving node with id = 10...\n", .{});
    const node_to_remove = tree.search(.{ .id = 10, .name = "" }) orelse {
        std.debug.print("Node not found!\n", .{});
        return;
    };
    tree.remove(node_to_remove);

    // Iterate again to show the node has been removed.
    std.debug.print("\nIn-order traversal after removal:\n", .{});
    var it_after_remove = tree.inorder();
    while (it_after_remove.next()) |node| {
        std.debug.print("\tid = {d}, name = {s}\n", .{ node.payload.id, node.payload.name });
    }
}
