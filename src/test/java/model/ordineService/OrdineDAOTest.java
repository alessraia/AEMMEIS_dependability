package model.ordineService;

import model.ConPool;
import model.libroService.Libro;
import org.junit.jupiter.api.*;
import org.mockito.MockedStatic;

import java.sql.*;
import java.time.LocalDate;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

/**
 * Test class for OrdineDAO
 * Tests all CRUD operations and business logic methods
 */
class OrdineDAOTest {

    private OrdineDAO ordineDAO;
    private Connection mockConnection;
    private PreparedStatement mockPreparedStatement;
    private ResultSet mockResultSet;
    private MockedStatic<ConPool> mockedConPool;
    private RigaOrdineDAO mockRigaOrdineDAO;

    @BeforeEach
    void setUp() throws SQLException {
        mockConnection = mock(Connection.class);
        mockPreparedStatement = mock(PreparedStatement.class);
        mockResultSet = mock(ResultSet.class);
        mockRigaOrdineDAO = mock(RigaOrdineDAO.class);
        
        ordineDAO = new OrdineDAO(mockRigaOrdineDAO);

        mockedConPool = mockStatic(ConPool.class);
        mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
    }

    @AfterEach
    void tearDown() {
        if (mockedConPool != null) {
            mockedConPool.close();
        }
    }

    // ==================== doSave Tests ====================

    @Test
    void testDoSave_Success() throws SQLException {
        // Arrange
        Ordine ordine = createValidOrdine();
        List<RigaOrdine> righeOrdine = new ArrayList<>();
        RigaOrdine riga = new RigaOrdine();
        riga.setIdOrdine("ORD001");
        Libro libro = new Libro();
        libro.setIsbn("1234567890123");
        riga.setLibro(libro);
        riga.setPrezzoUnitario(19.99);
        riga.setQuantita(2);
        righeOrdine.add(riga);
        ordine.setRigheOrdine(righeOrdine);

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);
        doNothing().when(mockRigaOrdineDAO).doSave(any(RigaOrdine.class));

        // Act
        assertDoesNotThrow(() -> ordineDAO.doSave(ordine));

        // Assert
        verify(mockPreparedStatement).setString(1, "ORD001");
        verify(mockPreparedStatement).setDouble(2, 99.99);
        verify(mockPreparedStatement).setString(3, "Via Roma 123");
        verify(mockPreparedStatement).setString(4, "Napoli");
        verify(mockPreparedStatement).setInt(5, 10);
        verify(mockPreparedStatement).setInt(6, 5);
        verify(mockPreparedStatement).setDate(7, Date.valueOf(LocalDate.of(2024, 1, 15)));
        verify(mockPreparedStatement).setString(8, "In Preparazione");
        verify(mockPreparedStatement).setString(9, "MAT001");
        verify(mockPreparedStatement).setString(10, "user@example.com");
        verify(mockPreparedStatement).executeUpdate();
        verify(mockRigaOrdineDAO).doSave(riga);
    }

    @Test
    void testDoSave_InsertFails() throws SQLException {
        // Arrange
        Ordine ordine = createValidOrdine();
        ordine.setRigheOrdine(new ArrayList<>());

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(0);

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, () -> ordineDAO.doSave(ordine));
        assertEquals("INSERT error.", exception.getMessage());
    }

    @Test
    void testDoSave_SQLException() throws SQLException {
        // Arrange
        Ordine ordine = createValidOrdine();
        ordine.setRigheOrdine(new ArrayList<>());

        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Database error"));

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, () -> ordineDAO.doSave(ordine));
        assertTrue(exception.getCause() instanceof SQLException);
    }

    // ==================== doRetrieveById Tests ====================

    @Test
    void testDoRetrieveById_Found() throws SQLException {
        // Arrange
        String idOrdine = "ORD001";
        setupMockResultSetForOrdine();

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true);
        when(mockRigaOrdineDAO.doRetrivedByOrdine(idOrdine)).thenReturn(new ArrayList<>());

        // Act
        Ordine result = ordineDAO.doRetrieveById(idOrdine);

        // Assert
        assertNotNull(result);
        assertEquals("ORD001", result.getIdOrdine());
        assertEquals(99.99, result.getCosto());
        assertEquals("Via Roma 123", result.getIndirizzoSpedizione());
        assertEquals("Napoli", result.getCitta());
        assertEquals(10, result.getPuntiOttenuti());
        assertEquals(5, result.getPuntiSpesi());
        assertEquals(LocalDate.of(2024, 1, 15), result.getDataEffettuazione());
        assertEquals("In Preparazione", result.getStato());
        assertEquals("MAT001", result.getMatricola());
        assertEquals("user@example.com", result.getEmail());
        verify(mockPreparedStatement).setString(1, idOrdine);
        verify(mockRigaOrdineDAO).doRetrivedByOrdine(idOrdine);
    }

    @Test
    void testDoRetrieveById_NotFound() throws SQLException {
        // Arrange
        String idOrdine = "NONEXISTENT";
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(false);

        // Act
        Ordine result = ordineDAO.doRetrieveById(idOrdine);

        // Assert
        assertNull(result);
        verify(mockPreparedStatement).setString(1, idOrdine);
    }

    @Test
    void testDoRetrieveById_WithNullDataArrivo() throws SQLException {
        // Arrange
        String idOrdine = "ORD001";
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true);
        when(mockResultSet.getString(1)).thenReturn("ORD001");
        when(mockResultSet.getDouble(2)).thenReturn(99.99);
        when(mockResultSet.getString(3)).thenReturn("Via Roma 123");
        when(mockResultSet.getString(4)).thenReturn("Napoli");
        when(mockResultSet.getInt(5)).thenReturn(10);
        when(mockResultSet.getInt(6)).thenReturn(5);
        when(mockResultSet.getDate(7)).thenReturn(null); // dataArrivo is null
        when(mockResultSet.getDate(8)).thenReturn(Date.valueOf(LocalDate.of(2024, 1, 15)));
        when(mockResultSet.getString(9)).thenReturn("In Preparazione");
        when(mockResultSet.getString(10)).thenReturn("MAT001");
        when(mockResultSet.getString(11)).thenReturn("user@example.com");
        when(mockRigaOrdineDAO.doRetrivedByOrdine(idOrdine)).thenReturn(new ArrayList<>());

        // Act
        Ordine result = ordineDAO.doRetrieveById(idOrdine);

        // Assert
        assertNotNull(result);
        assertNull(result.getDataArrivo());
    }

    @Test
    void testDoRetrieveById_SQLException() throws SQLException {
        // Arrange
        String idOrdine = "ORD001";
        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Database error"));

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, () -> ordineDAO.doRetrieveById(idOrdine));
        assertTrue(exception.getCause() instanceof SQLException);
    }

    // ==================== doRetrieveByUtente Tests ====================

    @Test
    void testDoRetrieveByUtente_Success() throws SQLException {
        // Arrange
        String email = "user@example.com";
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true, true, false);
        when(mockResultSet.getString(1)).thenReturn("ORD001", "ORD002");

        // Mock doRetrieveById calls
        OrdineDAO spyOrdineDAO = spy(new OrdineDAO(mockRigaOrdineDAO));
        Ordine ordine1 = createValidOrdine();
        ordine1.setIdOrdine("ORD001");
        Ordine ordine2 = createValidOrdine();
        ordine2.setIdOrdine("ORD002");
        doReturn(ordine1).when(spyOrdineDAO).doRetrieveById("ORD001");
        doReturn(ordine2).when(spyOrdineDAO).doRetrieveById("ORD002");

        // Act
        List<Ordine> result = spyOrdineDAO.doRetrieveByUtente(email);

        // Assert
        assertNotNull(result);
        assertEquals(2, result.size());
        assertEquals("ORD001", result.get(0).getIdOrdine());
        assertEquals("ORD002", result.get(1).getIdOrdine());
        verify(mockPreparedStatement).setString(1, email);
    }

    @Test
    void testDoRetrieveByUtente_NoResults() throws SQLException {
        // Arrange
        String email = "noorders@example.com";
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(false);

        // Act
        List<Ordine> result = ordineDAO.doRetrieveByUtente(email);

        // Assert
        assertNotNull(result);
        assertTrue(result.isEmpty());
        verify(mockPreparedStatement).setString(1, email);
    }

    @Test
    void testDoRetrieveByUtente_SQLException() throws SQLException {
        // Arrange
        String email = "user@example.com";
        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Database error"));

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, () -> ordineDAO.doRetrieveByUtente(email));
        assertTrue(exception.getCause() instanceof SQLException);
    }

    // ==================== updateOrdine Tests ====================

    @Test
    void testUpdateOrdine_Success() throws SQLException {
        // Arrange
        Ordine ordine = createValidOrdine();
        ordine.setDataArrivo(LocalDate.of(2024, 1, 20));
        ordine.setStato("Consegnato");

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        // Act
        assertDoesNotThrow(() -> ordineDAO.updateOrdine(ordine));

        // Assert
        verify(mockPreparedStatement).setString(1, "Consegnato");
        verify(mockPreparedStatement).setDate(2, Date.valueOf(LocalDate.of(2024, 1, 20)));
        verify(mockPreparedStatement).setString(3, "ORD001");
        verify(mockPreparedStatement).executeUpdate();
    }

    @Test
    void testUpdateOrdine_UpdateFails() throws SQLException {
        // Arrange
        Ordine ordine = createValidOrdine();
        ordine.setDataArrivo(LocalDate.of(2024, 1, 20));
        ordine.setStato("Consegnato");

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(0);

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, () -> ordineDAO.updateOrdine(ordine));
        assertEquals("UPDATE error.", exception.getMessage());
    }

    @Test
    void testUpdateOrdine_SQLException() throws SQLException {
        // Arrange
        Ordine ordine = createValidOrdine();
        ordine.setDataArrivo(LocalDate.of(2024, 1, 20));
        ordine.setStato("Consegnato");

        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Database error"));

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, () -> ordineDAO.updateOrdine(ordine));
        assertTrue(exception.getCause() instanceof SQLException);
    }

    // ==================== updateStato Tests ====================

    @Test
    void testUpdateStato_Success() throws SQLException {
        // Arrange
        Ordine ordine = createValidOrdine();
        ordine.setStato("In Spedizione");

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        // Act
        assertDoesNotThrow(() -> ordineDAO.updateStato(ordine));

        // Assert
        verify(mockPreparedStatement).setString(1, "In Spedizione");
        verify(mockPreparedStatement).setString(2, "ORD001");
        verify(mockPreparedStatement).executeUpdate();
    }

    @Test
    void testUpdateStato_UpdateFails() throws SQLException {
        // Arrange
        Ordine ordine = createValidOrdine();
        ordine.setStato("In Spedizione");

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(0);

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, () -> ordineDAO.updateStato(ordine));
        assertEquals("UPDATE error.", exception.getMessage());
    }

    @Test
    void testUpdateStato_SQLException() throws SQLException {
        // Arrange
        Ordine ordine = createValidOrdine();
        ordine.setStato("In Spedizione");

        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Database error"));

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, () -> ordineDAO.updateStato(ordine));
        assertTrue(exception.getCause() instanceof SQLException);
    }

    // ==================== updateOrdineMatricola Tests ====================

    @Test
    void testUpdateOrdineMatricola_Success() throws SQLException {
        // Arrange
        Ordine ordine = createValidOrdine();
        ordine.setMatricola("MAT002");

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        // Act
        assertDoesNotThrow(() -> ordineDAO.updateOrdineMatricola(ordine));

        // Assert
        verify(mockPreparedStatement).setString(1, "MAT002");
        verify(mockPreparedStatement).setString(2, "ORD001");
        verify(mockPreparedStatement).executeUpdate();
    }

    @Test
    void testUpdateOrdineMatricola_UpdateFails() throws SQLException {
        // Arrange
        Ordine ordine = createValidOrdine();
        ordine.setMatricola("MAT002");

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(0);

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, () -> ordineDAO.updateOrdineMatricola(ordine));
        assertEquals("UPDATE error.", exception.getMessage());
    }

    @Test
    void testUpdateOrdineMatricola_SQLException() throws SQLException {
        // Arrange
        Ordine ordine = createValidOrdine();
        ordine.setMatricola("MAT002");

        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Database error"));

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, () -> ordineDAO.updateOrdineMatricola(ordine));
        assertTrue(exception.getCause() instanceof SQLException);
    }

    // ==================== deleteOrdiniByEmail Tests ====================

    @Test
    void testDeleteOrdiniByEmail_Success() throws SQLException {
        // Arrange
        String email = "user@example.com";
        OrdineDAO spyOrdineDAO = spy(new OrdineDAO(mockRigaOrdineDAO));
        
        List<Ordine> ordini = new ArrayList<>();
        Ordine ordine1 = createValidOrdine();
        ordine1.setIdOrdine("ORD001");
        ordini.add(ordine1);
        
        doReturn(ordini).when(spyOrdineDAO).doRetrieveByUtente(email);
        doNothing().when(mockRigaOrdineDAO).deleteRigaOrdineByIdOrdine("ORD001");
        
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        // Act
        assertDoesNotThrow(() -> spyOrdineDAO.deleteOrdiniByEmail(email));

        // Assert
        verify(mockPreparedStatement).setString(1, email);
        verify(mockPreparedStatement).executeUpdate();
    }

    @Test
    void testDeleteOrdiniByEmail_DeleteFails() throws SQLException {
        // Arrange
        String email = "user@example.com";
        OrdineDAO spyOrdineDAO = spy(new OrdineDAO(mockRigaOrdineDAO));
        
        List<Ordine> ordini = new ArrayList<>();
        doReturn(ordini).when(spyOrdineDAO).doRetrieveByUtente(email);
        
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(0);

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, () -> spyOrdineDAO.deleteOrdiniByEmail(email));
        assertEquals("DELETE error.", exception.getMessage());
    }

    @Test
    void testDeleteOrdiniByEmail_SQLException() throws SQLException {
        // Arrange
        String email = "user@example.com";
        OrdineDAO spyOrdineDAO = spy(new OrdineDAO(mockRigaOrdineDAO));
        
        List<Ordine> ordini = new ArrayList<>();
        doReturn(ordini).when(spyOrdineDAO).doRetrieveByUtente(email);
        
        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Database error"));

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, () -> spyOrdineDAO.deleteOrdiniByEmail(email));
        assertTrue(exception.getCause() instanceof SQLException);
    }

    // ==================== deleteOrdine Tests ====================

    @Test
    void testDeleteOrdine_Success() throws SQLException {
        // Arrange
        String idOrdine = "ORD001";
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);
        doNothing().when(mockRigaOrdineDAO).deleteRigaOrdineByIdOrdine(idOrdine);

        // Act
        assertDoesNotThrow(() -> ordineDAO.deleteOrdine(idOrdine));

        // Assert
        verify(mockPreparedStatement).setString(1, idOrdine);
        verify(mockPreparedStatement).executeUpdate();
    }

    @Test
    void testDeleteOrdine_DeleteFails() throws SQLException {
        // Arrange
        String idOrdine = "ORD001";
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(0);
        doNothing().when(mockRigaOrdineDAO).deleteRigaOrdineByIdOrdine(idOrdine);

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, () -> ordineDAO.deleteOrdine(idOrdine));
        assertEquals("DELETE error.", exception.getMessage());
    }

    @Test
    void testDeleteOrdine_SQLException() throws SQLException {
        // Arrange
        String idOrdine = "ORD001";
        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Database error"));

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, () -> ordineDAO.deleteOrdine(idOrdine));
        assertTrue(exception.getCause() instanceof SQLException);
    }

    // ==================== doRetrivedAllByIdOrdini Tests ====================

    @Test
    void testDoRetrivedAllByIdOrdini_Success() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true, true, true, false);
        when(mockResultSet.getString(1)).thenReturn("ORD001", "ORD002", "ORD003");

        // Act
        List<String> result = ordineDAO.doRetrivedAllByIdOrdini();

        // Assert
        assertNotNull(result);
        assertEquals(3, result.size());
        assertEquals("ORD001", result.get(0));
        assertEquals("ORD002", result.get(1));
        assertEquals("ORD003", result.get(2));
    }

    @Test
    void testDoRetrivedAllByIdOrdini_EmptyResult() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(false);

        // Act
        List<String> result = ordineDAO.doRetrivedAllByIdOrdini();

        // Assert
        assertNotNull(result);
        assertTrue(result.isEmpty());
    }

    @Test
    void testDoRetrivedAllByIdOrdini_SQLException() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Database error"));

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, () -> ordineDAO.doRetrivedAllByIdOrdini());
        assertTrue(exception.getCause() instanceof SQLException);
    }

    // ==================== Helper Methods ====================

    private Ordine createValidOrdine() {
        Ordine ordine = new Ordine();
        ordine.setIdOrdine("ORD001");
        ordine.setCosto(99.99);
        ordine.setIndirizzoSpedizione("Via Roma 123");
        ordine.setCitta("Napoli");
        ordine.setPuntiOttenuti(10);
        ordine.setPuntiSpesi(5);
        ordine.setDataEffettuazione(LocalDate.of(2024, 1, 15));
        ordine.setStato("In Preparazione");
        ordine.setMatricola("MAT001");
        ordine.setEmail("user@example.com");
        return ordine;
    }

    private void setupMockResultSetForOrdine() throws SQLException {
        when(mockResultSet.getString(1)).thenReturn("ORD001");
        when(mockResultSet.getDouble(2)).thenReturn(99.99);
        when(mockResultSet.getString(3)).thenReturn("Via Roma 123");
        when(mockResultSet.getString(4)).thenReturn("Napoli");
        when(mockResultSet.getInt(5)).thenReturn(10);
        when(mockResultSet.getInt(6)).thenReturn(5);
        when(mockResultSet.getDate(7)).thenReturn(Date.valueOf(LocalDate.of(2024, 1, 20)));
        when(mockResultSet.getDate(8)).thenReturn(Date.valueOf(LocalDate.of(2024, 1, 15)));
        when(mockResultSet.getString(9)).thenReturn("In Preparazione");
        when(mockResultSet.getString(10)).thenReturn("MAT001");
        when(mockResultSet.getString(11)).thenReturn("user@example.com");
    }
}
