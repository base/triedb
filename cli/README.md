# CLI Tools for TrieDB #

Commands should be called from the `/cli` folder for an existing database. 

### Print Page ###
To print a single page of a database:  
`cargo run print -d <path to database> [-p <page_id of page to print>] [-o <output path>]`

To print the whole database, omit the `page_id`:  
`cargo run print -d <path to database>` 


### Print TrieValue Info ###
`cargo run trie-value -d <path to database> -i <node identifier> [-v <verbose options>]`

Node identifier must be in one of these formats:  
  1. Address (<0x40 hex chars>)  
  2. Address hash (<0x64 hex chars>)  
  3. Address hash + storage hash (<0x128 hex chars>)  
  4. Address with storage slot, space separated (<0x40 hex chars> <slot>)  

Verbose options vary the level of information written to file:  
  1. None: only the account/storage node information
  2. Verbose (-v verbose): Node information for every node accessed along path to specified node
  3. Extra Verbose (-v extra-verbose): Information for each page accessed followed by information for each node accessed from that page along path to specified node


### Print Root Page Info ###
Prints the state root, root subtrie page ID, and orphaned pages list.  
`cargo run root-page -d <path to database> [-o <output path>]`



