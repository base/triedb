#CLI Tools for TrieDB#

Commands should be called from the `/cli` folder for an existing database. 

###Print Page###
To print a single page of a database:
`cargo run print -d <path to database> [-p <page_id of page to print>] [-o <output path>]

To print the whole database, omit the `page_id `:
`cargo run print -d <path to database> 


###Print Account or Storage Node Info###
cargo run account -d <path to database> -a <account identifier> [-v <verbose options>]

Account identifier must be in one of these formats:
    1. Full hash (0x + 64 or 128 hex chars)
    2. Address (0x + 40 hex chars)
    3. Address with storage slot, space separated (0x + 40 hex chars  0x + variable length)

Verbose options vary the level of information written to file:
    1. None (no -v flag): only the account/storage node information
    2. Verbose (-v verbose): Node information for every node accessed along path to specified node
    3. Extra Verbose (-v extra-verbose): Information for each page accessed followed by information for each node accessed from that page along path to specified node




