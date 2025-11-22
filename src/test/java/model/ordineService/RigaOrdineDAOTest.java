package model.ordineService;

import model.ConPool;
import model.libroService.Libro;
import model.libroService.LibroDAO;
import org.junit.jupiter.api.*;
import org.mockito.MockedStatic;

import java.sql.*;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

/**
 * Test class for RigaOrdineDAO
 * Tests all CRUD operations for order line items
 */
class RigaOrdineDAOTest {

    private RigaOrdineDAO rigaOrdineDAO;
    private Connection mockConnection;
    private PreparedStatement mockPreparedStatement;
    private ResultSet mockResultSet;
    private MockedStatic<ConPool> mockedConPool;
    private LibroDAO mockLibroDAO;

    @BeforeEach
    void setUp() throws SQLException {
        mockConnection = mock(Connection.class);
        mockPreparedStatement = mock(PreparedStatement.class);
        mockResultSet = mock(ResultSet.class);
        mockLibroDAO = mock(LibroDAO.class);

        rigaOrdineDAO = new RigaOrdineDAO(mockLibroDAO);

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
        RigaOrdine rigaOrdine = createValidRigaOrdine();

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        // Act
        assertDoesNotThrow(() -> rigaOrdineDAO.doSave(rigaOrdine));

        // Assert
        verify(mockPreparedStatement).setString(1, "ORD001");
        verify(mockPreparedStatement).setString(2, "1234567890123");
        verify(mockPreparedStatement).setDouble(3, 19.99);
        verify(mockPreparedStatement).setInt(4, 2);
        verify(mockPreparedStatement).executeUpdate();
    }

    @Test
    void testDoSave_InsertFails() throws SQLException {
        // Arrange
        RigaOrdine rigaOrdine = createValidRigaOrdine();

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(0);

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, () -> rigaOrdineDAO.doSave(rigaOrdine));
        assertEquals("INSERT error.", exception.getMessage());
    }

    @Test
    void testDoSave_SQLException() throws SQLException {
        // Arrange
        RigaOrdine rigaOrdine = createValidRigaOrdine();

        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Database error"));

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, () -> rigaOrdineDAO.doSave(rigaOrdine));
        assertTrue(exception.getCause() instanceof SQLException);
    }

    // ==================== doRetrivedByOrdine Tests ====================

    @Test
    void testDoRetrivedByOrdine_Success() throws SQLException {
        // Arrange
        String idOrdine = "ORD001";
        Libro libro1 = createMockLibro("1234567890123");
        Libro libro2 = createMockLibro("9876543210987");

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true, true, false);
        when(mockResultSet.getString(1)).thenReturn("ORD001", "ORD001");
        when(mockResultSet.getString(2)).thenReturn("1234567890123", "9876543210987");
        when(mockResultSet.getDouble(3)).thenReturn(19.99, 29.99);
        when(mockResultSet.getInt(4)).thenReturn(2, 1);

        when(mockLibroDAO.doRetrieveById("1234567890123")).thenReturn(libro1);
        when(mockLibroDAO.doRetrieveById("9876543210987")).thenReturn(libro2);

        // Act
        List<RigaOrdine> result = rigaOrdineDAO.doRetrivedByOrdine(idOrdine);

        // Assert
        assertNotNull(result);
        assertEquals(2, result.size());
        
        assertEquals("ORD001", result.get(0).getIdOrdine());
        assertEquals("1234567890123", result.get(0).getLibro().getIsbn());
        assertEquals(19.99, result.get(0).getPrezzoUnitario());
        assertEquals(2, result.get(0).getQuantita());

        assertEquals("ORD001", result.get(1).getIdOrdine());
        assertEquals("9876543210987", result.get(1).getLibro().getIsbn());
        assertEquals(29.99, result.get(1).getPrezzoUnitario());
        assertEquals(1, result.get(1).getQuantita());

        verify(mockPreparedStatement).setString(1, idOrdine);
        verify(mockLibroDAO).doRetrieveById("1234567890123");
        verify(mockLibroDAO).doRetrieveById("9876543210987");
    }

    @Test
    void testDoRetrivedByOrdine_EmptyResult() throws SQLException {
        // Arrange
        String idOrdine = "ORD999";
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(false);

        // Act
        List<RigaOrdine> result = rigaOrdineDAO.doRetrivedByOrdine(idOrdine);

        // Assert
        assertNotNull(result);
        assertTrue(result.isEmpty());
        verify(mockPreparedStatement).setString(1, idOrdine);
    }

    @Test
    void testDoRetrivedByOrdine_SQLException() throws SQLException {
        // Arrange
        String idOrdine = "ORD001";
        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Database error"));

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, 
            () -> rigaOrdineDAO.doRetrivedByOrdine(idOrdine));
        assertTrue(exception.getCause() instanceof SQLException);
    }

    // ==================== doRetriveById Tests ====================

    @Test
    void testDoRetriveById_Found() throws SQLException {
        // Arrange
        String idOrdine = "ORD001";
        String isbn = "1234567890123";
        Libro libro = createMockLibro(isbn);

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true);
        when(mockResultSet.getString(1)).thenReturn("ORD001");
        when(mockResultSet.getString(2)).thenReturn("1234567890123");
        when(mockResultSet.getDouble(3)).thenReturn(19.99);
        when(mockResultSet.getInt(4)).thenReturn(2);

        when(mockLibroDAO.doRetrieveById(isbn)).thenReturn(libro);

        // Act
        RigaOrdine result = rigaOrdineDAO.doRetriveById(idOrdine, isbn);

        // Assert
        assertNotNull(result);
        assertEquals("ORD001", result.getIdOrdine());
        assertEquals("1234567890123", result.getLibro().getIsbn());
        assertEquals(19.99, result.getPrezzoUnitario());
        assertEquals(2, result.getQuantita());

        verify(mockPreparedStatement).setString(1, idOrdine);
        verify(mockPreparedStatement).setString(2, isbn);
        verify(mockLibroDAO).doRetrieveById(isbn);
    }

    @Test
    void testDoRetriveById_NotFound() throws SQLException {
        // Arrange
        String idOrdine = "ORD001";
        String isbn = "9999999999999";

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(false);

        // Act
        RigaOrdine result = rigaOrdineDAO.doRetriveById(idOrdine, isbn);

        // Assert
        assertNull(result);
        verify(mockPreparedStatement).setString(1, idOrdine);
        verify(mockPreparedStatement).setString(2, isbn);
    }

    @Test
    void testDoRetriveById_SQLException() throws SQLException {
        // Arrange
        String idOrdine = "ORD001";
        String isbn = "1234567890123";

        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Database error"));

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, 
            () -> rigaOrdineDAO.doRetriveById(idOrdine, isbn));
        assertTrue(exception.getCause() instanceof SQLException);
    }

    // ==================== deleteRigaOrdine Tests ====================

    @Test
    void testDeleteRigaOrdine_Success() throws SQLException {
        // Arrange
        String isbn = "1234567890123";
        String idOrdine = "ORD001";

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        // Act
        assertDoesNotThrow(() -> rigaOrdineDAO.deleteRigaOrdine(isbn, idOrdine));

        // Assert
        verify(mockPreparedStatement).setString(1, idOrdine);
        verify(mockPreparedStatement).setString(2, isbn);
        verify(mockPreparedStatement).executeUpdate();
    }

    @Test
    void testDeleteRigaOrdine_DeleteFails() throws SQLException {
        // Arrange
        String isbn = "1234567890123";
        String idOrdine = "ORD001";

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(0);

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, 
            () -> rigaOrdineDAO.deleteRigaOrdine(isbn, idOrdine));
        assertEquals("DELETE error.", exception.getMessage());
    }

    @Test
    void testDeleteRigaOrdine_SQLException() throws SQLException {
        // Arrange
        String isbn = "1234567890123";
        String idOrdine = "ORD001";

        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Database error"));

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, 
            () -> rigaOrdineDAO.deleteRigaOrdine(isbn, idOrdine));
        assertTrue(exception.getCause() instanceof SQLException);
    }

    // ==================== deleteRigaOrdineByIdOrdine Tests ====================

    @Test
    void testDeleteRigaOrdineByIdOrdine_Success() throws SQLException {
        // Arrange
        String idOrdine = "ORD001";

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(2); // Deleted 2 rows

        // Act
        assertDoesNotThrow(() -> rigaOrdineDAO.deleteRigaOrdineByIdOrdine(idOrdine));

        // Assert
        verify(mockPreparedStatement).setString(1, idOrdine);
        verify(mockPreparedStatement).executeUpdate();
    }

    @Test
    void testDeleteRigaOrdineByIdOrdine_SingleRow() throws SQLException {
        // Arrange
        String idOrdine = "ORD001";

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        // Act
        assertDoesNotThrow(() -> rigaOrdineDAO.deleteRigaOrdineByIdOrdine(idOrdine));

        // Assert
        verify(mockPreparedStatement).setString(1, idOrdine);
        verify(mockPreparedStatement).executeUpdate();
    }

    @Test
    void testDeleteRigaOrdineByIdOrdine_NoRowsDeleted() throws SQLException {
        // Arrange
        String idOrdine = "ORD999";

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(0);

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, 
            () -> rigaOrdineDAO.deleteRigaOrdineByIdOrdine(idOrdine));
        assertEquals("DELETE error.", exception.getMessage());
    }

    @Test
    void testDeleteRigaOrdineByIdOrdine_SQLException() throws SQLException {
        // Arrange
        String idOrdine = "ORD001";

        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Database error"));

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, 
            () -> rigaOrdineDAO.deleteRigaOrdineByIdOrdine(idOrdine));
        assertTrue(exception.getCause() instanceof SQLException);
    }

    // ==================== Helper Methods ====================

    private RigaOrdine createValidRigaOrdine() {
        RigaOrdine rigaOrdine = new RigaOrdine();
        rigaOrdine.setIdOrdine("ORD001");
        
        Libro libro = new Libro();
        libro.setIsbn("1234567890123");
        rigaOrdine.setLibro(libro);
        
        rigaOrdine.setPrezzoUnitario(19.99);
        rigaOrdine.setQuantita(2);
        
        return rigaOrdine;
    }

    private Libro createMockLibro(String isbn) {
        Libro libro = new Libro();
        libro.setIsbn(isbn);
        libro.setTitolo("Test Book");
        libro.setPrezzo(19.99);
        return libro;
    }
}
