import type { ExplorerNode, ChildEntry } from '../types';

interface NodeComponentProps {
  node: ExplorerNode;
  basePath: string;
  isExpanded: boolean;
  onToggle: () => void;
  onNavigate: (pageId: number, basePath?: string) => void;
}

export function NodeComponent({ node, basePath, isExpanded, onToggle, onNavigate }: NodeComponentProps) {
  const nodeTypeClass = node.nodeType.toLowerCase().replace('leaf', '-leaf');
  const fullPath = basePath + (node.prefix || '');

  return (
    <div className="node-item">
      <div className="node-header" onClick={onToggle}>
        <span className={`expand-icon ${isExpanded ? 'expanded' : ''}`}>&#9654;</span>
        <span className={`node-type ${nodeTypeClass}`}>{node.nodeType}</span>
        <span className="node-path">
          {fullPath ? (
            <>
              0x{basePath && <span className="path-base">{basePath}</span>}
              {node.prefix && <span className="path-prefix">{node.prefix}</span>}
            </>
          ) : (
            '(empty path)'
          )}
        </span>
        <span className="node-location">
          Cell {node.cellIndex} | {node.sizeBytes} bytes
        </span>
      </div>

      {isExpanded && (
        <>
          <div className="node-details">
            <dl>
              {node.nodeType === 'AccountLeaf' && (
                <>
                  <dt>Nonce</dt>
                  <dd>{node.nonce}</dd>
                  <dt>Balance</dt>
                  <dd>{node.balance}</dd>
                  <dt>Code Hash</dt>
                  <dd>0x{node.codeHash}</dd>
                  {node.storageRoot && (
                    <>
                      <dt>Storage Root</dt>
                      <dd>
                        <PointerLink
                          pointer={node.storageRoot}
                          onNavigate={onNavigate}
                        />
                      </dd>
                    </>
                  )}
                </>
              )}
              {node.nodeType === 'StorageLeaf' && (
                <>
                  <dt>Value</dt>
                  <dd>{node.value}</dd>
                </>
              )}
            </dl>
          </div>

          {node.nodeType === 'Branch' && node.children && node.children.length > 0 && (
            <div className="node-children">
              <div className="child-list">
                {node.children.map((child) => (
                  <ChildPointer key={child.index} child={child} fullPath={fullPath} onNavigate={onNavigate} />
                ))}
              </div>
            </div>
          )}
        </>
      )}
    </div>
  );
}

interface PointerLinkProps {
  pointer: { locationType: string; pageId?: number; cellIndex?: number; rlpHash?: string };
  onNavigate: (pageId: number, basePath?: string) => void;
}

function PointerLink({ pointer, onNavigate }: PointerLinkProps) {
  if (pointer.locationType === 'SamePage' && pointer.cellIndex !== undefined) {
    return (
      <span
        className="child-pointer same-page"
        onClick={(e) => {
          e.stopPropagation();
          // Scroll to cell on same page - for now just highlight
        }}
      >
        Cell {pointer.cellIndex}
      </span>
    );
  } else if (pointer.locationType === 'OtherPage' && pointer.pageId !== undefined) {
    return (
      <span
        className="child-pointer other-page"
        onClick={(e) => {
          e.stopPropagation();
          // Storage root pointers start a new trie, so empty base path
          onNavigate(pointer.pageId!, '');
        }}
      >
        Page {pointer.pageId}
      </span>
    );
  }
  return <span className="child-pointer">Unknown</span>;
}

interface ChildPointerProps {
  child: ChildEntry;
  fullPath: string;
  onNavigate: (pageId: number, basePath?: string) => void;
}

function ChildPointer({ child, fullPath, onNavigate }: ChildPointerProps) {
  const nibble = child.index.toString(16).toUpperCase();
  const pointer = child.pointer;
  // The child's base path is the parent's full path + this nibble
  const childBasePath = fullPath + nibble;

  if (pointer.locationType === 'SamePage' && pointer.cellIndex !== undefined) {
    return (
      <span
        className="child-pointer same-page"
        onClick={() => {
          // For same-page navigation, could scroll to node
        }}
      >
        [{nibble}] Cell {pointer.cellIndex}
      </span>
    );
  } else if (pointer.locationType === 'OtherPage' && pointer.pageId !== undefined) {
    return (
      <span
        className="child-pointer other-page"
        onClick={() => onNavigate(pointer.pageId!, childBasePath)}
      >
        [{nibble}] Page {pointer.pageId}
      </span>
    );
  }
  return (
    <span className="child-pointer">
      [{nibble}] Unknown
    </span>
  );
}
