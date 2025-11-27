package model.tesseraService;

import model.ConPool;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.MockedStatic;

import java.sql.Connection;
import java.sql.Date;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.time.LocalDate;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

class TesseraDAOTest {

    private TesseraDAO tesseraDAO;
    private Connection mockConnection;
    private PreparedStatement mockPreparedStatement;
    private ResultSet mockResultSet;

    @BeforeEach
    void setUp() {
        tesseraDAO = new TesseraDAO();
        mockConnection = mock(Connection.class);
        mockPreparedStatement = mock(PreparedStatement.class);
        mockResultSet = mock(ResultSet.class);
    }

    // ==================== Tests for doSave ====================

    @Test
    void testDoSave_Success() throws SQLException {
        LocalDate today = LocalDate.now();
        Tessera tessera = new Tessera();
        tessera.setNumero("TESS001");
        tessera.setDataCreazione(today);
        tessera.setDataScadenza(today.plusYears(2));
        tessera.setEmail("test@example.com");

        // Create separate mocks for INSERT and SELECT statements
        PreparedStatement insertPs = mock(PreparedStatement.class);
        PreparedStatement selectPs = mock(PreparedStatement.class);

        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            // Return different PreparedStatements based on SQL
            when(mockConnection.prepareStatement(contains("INSERT"))).thenReturn(insertPs);
            when(mockConnection.prepareStatement(contains("SELECT"))).thenReturn(selectPs);
            
            when(insertPs.executeUpdate()).thenReturn(1);
            when(selectPs.executeQuery()).thenReturn(mockResultSet);
            when(mockResultSet.next()).thenReturn(true);
            when(mockResultSet.getString(1)).thenReturn("TESS001");
            when(mockResultSet.getDate(2)).thenReturn(Date.valueOf(today));
            when(mockResultSet.getDate(3)).thenReturn(Date.valueOf(today.plusYears(2)));
            when(mockResultSet.getInt(4)).thenReturn(50);
            when(mockResultSet.getString(5)).thenReturn("test@example.com");

            assertDoesNotThrow(() -> tesseraDAO.doSave(tessera));
            
            // Verify INSERT PreparedStatement parameters are set correctly
            verify(insertPs).setString(1, "TESS001");
            verify(insertPs).setDate(2, Date.valueOf(today));
            verify(insertPs).setDate(3, Date.valueOf(today.plusYears(2)));
            verify(insertPs).setString(4, "test@example.com");
            verify(insertPs).executeUpdate();
            
            // Verify punti is set after save
            assertEquals(50, tessera.getPunti());
        }
    }

    @Test
    void testDoSave_InsertError() throws SQLException {
        LocalDate today = LocalDate.now();
        Tessera tessera = new Tessera();
        tessera.setNumero("TESS002");
        tessera.setDataCreazione(today);
        tessera.setDataScadenza(today.plusYears(2));
        tessera.setEmail("test2@example.com");

        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeUpdate()).thenReturn(0);

            RuntimeException exception = assertThrows(RuntimeException.class, () -> tesseraDAO.doSave(tessera));
            assertEquals("INSERT error.", exception.getMessage());
        }
    }

    @Test
    void testDoSave_SQLExceptionThrown() throws SQLException {
        LocalDate today = LocalDate.now();
        Tessera tessera = new Tessera();
        tessera.setNumero("TESS003");
        tessera.setDataCreazione(today);
        tessera.setDataScadenza(today.plusYears(2));
        tessera.setEmail("test3@example.com");

        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Connection error"));

            assertThrows(RuntimeException.class, () -> tesseraDAO.doSave(tessera));
        }
    }

    // ==================== Tests for deleteTessera ====================

    @Test
    void testDeleteTessera_Success() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeUpdate()).thenReturn(1);

            assertDoesNotThrow(() -> tesseraDAO.deleteTessera("TESS001"));
            verify(mockConnection).prepareStatement("DELETE FROM Tessera WHERE numero=?");
            verify(mockPreparedStatement).setString(1, "TESS001");
        }
    }

    @Test
    void testDeleteTessera_NoRowsDeleted() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeUpdate()).thenReturn(0);

            RuntimeException exception = assertThrows(RuntimeException.class, () -> tesseraDAO.deleteTessera("TESS_NONEXISTENT"));
            assertEquals("DELETE error.", exception.getMessage());
        }
    }

    @Test
    void testDeleteTessera_SQLExceptionThrown() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("DB error"));

            assertThrows(RuntimeException.class, () -> tesseraDAO.deleteTessera("TESS001"));
        }
    }

    // ==================== Tests for updateTessera ====================

    @Test
    void testUpdateTessera_Success() throws SQLException {
        Tessera tessera = new Tessera();
        tessera.setNumero("TESS001");
        tessera.setPunti(150);

        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeUpdate()).thenReturn(1);

            assertDoesNotThrow(() -> tesseraDAO.updateTessera(tessera));
            verify(mockConnection).prepareStatement("UPDATE Tessera SET punti = ? WHERE numero = ?");
            verify(mockPreparedStatement).setInt(1, 150);
            verify(mockPreparedStatement).setString(2, "TESS001");
        }
    }

    @Test
    void testUpdateTessera_NoRowsUpdated() throws SQLException {
        Tessera tessera = new Tessera();
        tessera.setNumero("TESS_NONEXISTENT");
        tessera.setPunti(100);

        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeUpdate()).thenReturn(0);

            RuntimeException exception = assertThrows(RuntimeException.class, () -> tesseraDAO.updateTessera(tessera));
            assertEquals("UPDATE error.", exception.getMessage());
        }
    }

    @Test
    void testUpdateTessera_SQLExceptionThrown() throws SQLException {
        Tessera tessera = new Tessera();
        tessera.setNumero("TESS001");
        tessera.setPunti(200);

        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Update failed"));

            assertThrows(RuntimeException.class, () -> tesseraDAO.updateTessera(tessera));
        }
    }

    // ==================== Tests for doRetrivedAll ====================

    @Test
    void testDoRetrivedAll_MultipleTessere() throws SQLException {
        LocalDate today = LocalDate.now();

        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);

            when(mockResultSet.next())
                    .thenReturn(true)
                    .thenReturn(true)
                    .thenReturn(false);
            when(mockResultSet.getString(1))
                    .thenReturn("TESS001")
                    .thenReturn("TESS002");
            when(mockResultSet.getDate(2))
                    .thenReturn(Date.valueOf(today))
                    .thenReturn(Date.valueOf(today));
            when(mockResultSet.getDate(3))
                    .thenReturn(Date.valueOf(today.plusYears(2)))
                    .thenReturn(Date.valueOf(today.plusYears(2)));
            when(mockResultSet.getInt(4))
                    .thenReturn(50)
                    .thenReturn(100);
            when(mockResultSet.getString(5))
                    .thenReturn("user1@example.com")
                    .thenReturn("user2@example.com");

            List<Tessera> result = tesseraDAO.doRetrivedAll();

            assertNotNull(result);
            assertEquals(2, result.size());
            assertEquals("TESS001", result.get(0).getNumero());
            assertEquals(50, result.get(0).getPunti());
            // Verify dates and email are properly set
            assertEquals(today, result.get(0).getDataCreazione());
            assertEquals(today.plusYears(2), result.get(0).getDataScadenza());
            assertEquals("user1@example.com", result.get(0).getEmail());
            assertEquals("TESS002", result.get(1).getNumero());
            assertEquals(today, result.get(1).getDataCreazione());
            assertEquals(today.plusYears(2), result.get(1).getDataScadenza());
            assertEquals("user2@example.com", result.get(1).getEmail());
        }
    }

    @Test
    void testDoRetrivedAll_Empty() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
            when(mockResultSet.next()).thenReturn(false);

            List<Tessera> result = tesseraDAO.doRetrivedAll();

            assertNotNull(result);
            assertTrue(result.isEmpty());
        }
    }

    @Test
    void testDoRetrivedAll_SQLExceptionThrown() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Query failed"));

            assertThrows(RuntimeException.class, () -> tesseraDAO.doRetrivedAll());
        }
    }

    // ==================== Tests for doRetrivedAllByNumero ====================

    @Test
    void testDoRetrivedAllByNumero_MultipleTessere() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);

            when(mockResultSet.next())
                    .thenReturn(true)
                    .thenReturn(true)
                    .thenReturn(true)
                    .thenReturn(false);
            when(mockResultSet.getString(1))
                    .thenReturn("TESS001")
                    .thenReturn("TESS002")
                    .thenReturn("TESS003");

            List<String> result = tesseraDAO.doRetrivedAllByNumero();

            assertNotNull(result);
            assertEquals(3, result.size());
            // Verify exact order and content to kill timed_out mutation
            assertEquals("TESS001", result.get(0));
            assertEquals("TESS002", result.get(1));
            assertEquals("TESS003", result.get(2));
            assertTrue(result.contains("TESS001"));
            assertTrue(result.contains("TESS002"));
            assertTrue(result.contains("TESS003"));
        }
    }

    @Test
    void testDoRetrivedAllByNumero_Empty() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
            when(mockResultSet.next()).thenReturn(false);

            List<String> result = tesseraDAO.doRetrivedAllByNumero();

            assertNotNull(result);
            assertTrue(result.isEmpty());
        }
    }

    @Test
    void testDoRetrivedAllByNumero_SQLExceptionThrown() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Query failed"));

            assertThrows(RuntimeException.class, () -> tesseraDAO.doRetrivedAllByNumero());
        }
    }

    // ==================== Tests for doRetrieveById ====================

    @Test
    void testDoRetrieveById_Success() throws SQLException {
        LocalDate today = LocalDate.now();

        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);

            when(mockResultSet.next()).thenReturn(true);
            when(mockResultSet.getString(1)).thenReturn("TESS001");
            when(mockResultSet.getDate(2)).thenReturn(Date.valueOf(today));
            when(mockResultSet.getDate(3)).thenReturn(Date.valueOf(today.plusYears(2)));
            when(mockResultSet.getInt(4)).thenReturn(150);
            when(mockResultSet.getString(5)).thenReturn("test@example.com");

            Tessera result = tesseraDAO.doRetrieveById("TESS001");

            assertNotNull(result);
            assertEquals("TESS001", result.getNumero());
            assertEquals(150, result.getPunti());
            assertEquals("test@example.com", result.getEmail());
            // Verify date fields are properly set
            assertEquals(today, result.getDataCreazione());
            assertEquals(today.plusYears(2), result.getDataScadenza());
            verify(mockPreparedStatement).setString(1, "TESS001");
        }
    }

    @Test
    void testDoRetrieveById_NotFound() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
            when(mockResultSet.next()).thenReturn(false);

            Tessera result = tesseraDAO.doRetrieveById("TESS_NONEXISTENT");

            assertNull(result);
            verify(mockPreparedStatement).setString(1, "TESS_NONEXISTENT");
        }
    }

    @Test
    void testDoRetrieveById_SQLExceptionThrown() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Query error"));

            assertThrows(RuntimeException.class, () -> tesseraDAO.doRetrieveById("TESS001"));
        }
    }

    // ==================== Tests for doRetrieveByEmail ====================

    @Test
    void testDoRetrieveByEmail_Success() throws SQLException {
        LocalDate today = LocalDate.now();

        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);

            when(mockResultSet.next()).thenReturn(true);
            when(mockResultSet.getString(1)).thenReturn("TESS001");
            when(mockResultSet.getDate(2)).thenReturn(Date.valueOf(today));
            when(mockResultSet.getDate(3)).thenReturn(Date.valueOf(today.plusYears(2)));
            when(mockResultSet.getInt(4)).thenReturn(100);
            when(mockResultSet.getString(5)).thenReturn("user@example.com");

            Tessera result = tesseraDAO.doRetrieveByEmail("user@example.com");

            assertNotNull(result);
            assertEquals("TESS001", result.getNumero());
            assertEquals("user@example.com", result.getEmail());
            assertEquals(100, result.getPunti());
            // Verify date fields are properly set
            assertEquals(today, result.getDataCreazione());
            assertEquals(today.plusYears(2), result.getDataScadenza());
            verify(mockPreparedStatement).setString(1, "user@example.com");
        }
    }

    @Test
    void testDoRetrieveByEmail_NotFound() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
            when(mockResultSet.next()).thenReturn(false);

            Tessera result = tesseraDAO.doRetrieveByEmail("nonexistent@example.com");

            assertNull(result);
            verify(mockPreparedStatement).setString(1, "nonexistent@example.com");
        }
    }

    @Test
    void testDoRetrieveByEmail_SQLExceptionThrown() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Query error"));

            assertThrows(RuntimeException.class, () -> tesseraDAO.doRetrieveByEmail("test@example.com"));
        }
    }

}
