import React, { useState } from 'react';
import * as api from '../api/client';
import type { PathSearchResult } from '../types';

interface SearchBarProps {
  onSearchResult: (result: PathSearchResult | null) => void;
}

export function SearchBar({ onSearchResult }: SearchBarProps) {
  const [query, setQuery] = useState('');
  const [searchType, setSearchType] = useState<'raw' | 'address' | 'storage'>('raw');
  const [isSearching, setIsSearching] = useState(false);

  const handleSearch = async () => {
    if (!query.trim()) return;

    setIsSearching(true);
    try {
      const response = await api.search(query, searchType);
      if (response.success && response.data) {
        onSearchResult(response.data);
      } else {
        onSearchResult(null);
      }
    } catch (e) {
      console.error('Search failed:', e);
      onSearchResult(null);
    } finally {
      setIsSearching(false);
    }
  };

  const handleKeyDown = (e: React.KeyboardEvent) => {
    if (e.key === 'Enter') {
      handleSearch();
    }
  };

  return (
    <div className="search-bar">
      <select value={searchType} onChange={(e) => setSearchType(e.target.value as typeof searchType)}>
        <option value="raw">Raw Path</option>
        <option value="address">Address</option>
        <option value="storage">Storage</option>
      </select>
      <input
        type="text"
        value={query}
        onChange={(e) => setQuery(e.target.value)}
        onKeyDown={handleKeyDown}
        placeholder={
          searchType === 'address'
            ? '0x... (Ethereum address)'
            : searchType === 'storage'
            ? 'address:slot (e.g., 0x...:0x0)'
            : '0x... (raw path, or 0xAccount:0xStorage)'
        }
      />
      <button onClick={handleSearch} disabled={isSearching}>
        {isSearching ? 'Searching...' : 'Search'}
      </button>
    </div>
  );
}
