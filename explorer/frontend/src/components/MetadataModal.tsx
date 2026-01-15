import { useState, useEffect } from 'react';
import type { DatabaseInfo } from '../types';
import * as api from '../api/client';

interface MetadataModalProps {
  isOpen: boolean;
  onClose: () => void;
}

export function MetadataModal({ isOpen, onClose }: MetadataModalProps) {
  const [metadata, setMetadata] = useState<DatabaseInfo | null>(null);
  const [isLoading, setIsLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);

  useEffect(() => {
    if (isOpen && !metadata) {
      loadMetadata();
    }
  }, [isOpen]);

  const loadMetadata = async () => {
    setIsLoading(true);
    setError(null);
    try {
      const response = await api.getMetadata();
      if (response.success && response.data) {
        setMetadata(response.data);
      } else {
        setError(response.error || 'Failed to load metadata');
      }
    } catch (e) {
      setError(e instanceof Error ? e.message : 'Unknown error');
    } finally {
      setIsLoading(false);
    }
  };

  if (!isOpen) return null;

  return (
    <div className="modal-overlay" onClick={onClose}>
      <div className="modal" onClick={(e) => e.stopPropagation()}>
        <div className="modal-header">
          <h2>Database Metadata</h2>
          <button className="modal-close" onClick={onClose}>
            &times;
          </button>
        </div>
        <div className="modal-body">
          {isLoading && <div className="loading">Loading metadata...</div>}
          {error && <div className="error">{error}</div>}
          {metadata && (
            <>
              <div className="metadata-section">
                <h3>Database Info</h3>
                <dl className="metadata-grid">
                  <dt>Snapshot ID</dt>
                  <dd>{metadata.snapshotId}</dd>
                  <dt>State Root</dt>
                  <dd>0x{metadata.rootNodeHash}</dd>
                  <dt>Root Page ID</dt>
                  <dd>{metadata.rootNodePageId ?? 'None'}</dd>
                  <dt>Total Pages</dt>
                  <dd>{metadata.totalPageCount}</dd>
                </dl>
              </div>

              <div className="metadata-section">
                <h3>Orphaned Pages ({metadata.orphanedPages.length})</h3>
                {metadata.orphanedPages.length > 0 ? (
                  <div className="orphan-list">
                    {metadata.orphanedPages.map((orphan) => (
                      <div key={orphan.pageId} className="orphan-item">
                        <span>Page {orphan.pageId}</span>
                        <span>Orphaned at snapshot {orphan.orphanedAtSnapshot}</span>
                      </div>
                    ))}
                  </div>
                ) : (
                  <div className="empty-message">No orphaned pages</div>
                )}
              </div>
            </>
          )}
        </div>
      </div>
    </div>
  );
}
