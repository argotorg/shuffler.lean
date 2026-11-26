//! Fixture of the suite zighint: methods of a struct (with the C and the internal calling convention), a nested struct
//! and a top-level function. Its Zig form is `methods-zig-hints.json` (made by scripts/zig-air/types.sh).

const Set = extern struct {
    n: u64,

    pub fn add(self: *Set, x: u64) callconv(.c) void {
        self.n +%= x;
    }

    pub fn size(self: *const Set) u64 {
        return self.n;
    }

    pub const Inner = struct {
        m: u64,

        pub fn get(self: *const Inner) callconv(.c) u64 {
            return self.m;
        }
    };
};

export fn total(s: *const Set, x: u64) callconv(.c) u64 {
    return s.n +% x;
}
