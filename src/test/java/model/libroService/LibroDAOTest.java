package model.libroService;

import model.ConPool;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.MockedConstruction;
import org.mockito.MockedStatic;
import org.mockito.Mockito;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

/**
 * Test class for LibroDAO
 * Tests all CRUD operations and book management methods
 */
class LibroDAOTest {

    private LibroDAO libroDAO;
    private Connection mockConnection;
    private PreparedStatement mockPreparedStatement;
    private ResultSet mockResultSet;
    private MockedStatic<ConPool> mockedConPool;

    @BeforeEach
    void setUp() throws SQLException {
        mockConnection = mock(Connection.class);
        mockPreparedStatement = mock(PreparedStatement.class);
        mockResultSet = mock(ResultSet.class);
        
        libroDAO = new LibroDAO();
        
        mockedConPool = mockStatic(ConPool.class);
        mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
    }

    @AfterEach
    void tearDown() {
        if (mockedConPool != null) {
            mockedConPool.close();
        }
    }

    // ==================== Helper Methods ====================

    private Libro createTestLibro(String isbn, String titolo, double prezzo, int sconto) {
        Libro libro = new Libro();
        libro.setIsbn(isbn);
        libro.setTitolo(titolo);
        libro.setGenere("Genere");
        libro.setAnnoPubblicazioni("2025");
        libro.setPrezzo(prezzo);
        libro.setSconto(sconto);
        libro.setTrama("Trama");
        libro.setImmagine("img.png");
        return libro;
    }

    // ==================== doRetrieveById Tests ====================

    @Test
    void testDoRetrieveById_Found() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true);
        when(mockResultSet.getString(1)).thenReturn("ISBN1");
        when(mockResultSet.getString(2)).thenReturn("Titolo");
        when(mockResultSet.getString(3)).thenReturn("Genere");
        when(mockResultSet.getString(4)).thenReturn("2020");
        when(mockResultSet.getDouble(5)).thenReturn(12.5);
        when(mockResultSet.getInt(6)).thenReturn(10);
        when(mockResultSet.getString(7)).thenReturn("Trama");
        when(mockResultSet.getString(8)).thenReturn("img.png");
        when(mockResultSet.getBoolean(9)).thenReturn(true);

        LibroDAO spyDao = spy(libroDAO);
        Autore a = new Autore();
        a.setCf("CF1");
        List<Autore> authors = new ArrayList<>();
        authors.add(a);
        doReturn(authors).when(spyDao).getScrittura("ISBN1");

        // Act
        Libro result = spyDao.doRetrieveById("ISBN1");

        // Assert
        assertNotNull(result);
        assertEquals("ISBN1", result.getIsbn());
        assertEquals("Titolo", result.getTitolo());
        assertEquals(12.5, result.getPrezzo());
        assertEquals(1, result.getAutori().size());
    }

    @Test
    void testDoRetrieveById_NotFound() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(false);

        // Act
        Libro result = libroDAO.doRetrieveById("NOISBN");

        // Assert
        assertNull(result);
    }

    // ==================== doRetriveAll Tests ====================

    @Test
    void testDoRetriveAll_ReturnsList() throws SQLException {
        // Arrange
        PreparedStatement psAll = mock(PreparedStatement.class);
        PreparedStatement psScr = mock(PreparedStatement.class);
        ResultSet rsAll = mock(ResultSet.class);
        ResultSet rsScr = mock(ResultSet.class);

        when(mockConnection.prepareStatement(contains("SELECT * FROM Libro"))).thenReturn(psAll);
        when(mockConnection.prepareStatement(contains("FROM Scrittura"))).thenReturn(psScr);

        when(psAll.executeQuery()).thenReturn(rsAll);
        when(rsAll.next()).thenReturn(true, false);
        when(rsAll.getString(1)).thenReturn("ISBNA");
        when(rsAll.getString(2)).thenReturn("TitA");
        when(rsAll.getString(3)).thenReturn("G");
        when(rsAll.getString(4)).thenReturn("2019");
        when(rsAll.getDouble(5)).thenReturn(7.5);
        when(rsAll.getInt(6)).thenReturn(0);
        when(rsAll.getString(7)).thenReturn("tr");
        when(rsAll.getString(8)).thenReturn("img");
        when(rsAll.getBoolean(9)).thenReturn(true);

        when(psScr.executeQuery()).thenReturn(rsScr);
        when(rsScr.next()).thenReturn(false);

        // Act
        List<Libro> list = libroDAO.doRetriveAll();

        // Assert
        assertNotNull(list);
        assertEquals(1, list.size());
        assertEquals("ISBNA", list.get(0).getIsbn());
    }

    // ==================== Search Tests ====================

    @Test
    void testSearch_ReturnsList() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true, true, false);
        when(mockResultSet.getString(1)).thenReturn("ISBN1", "ISBN2");
        when(mockResultSet.getString(2)).thenReturn("T1", "T2");
        when(mockResultSet.getString(3)).thenReturn("G1", "G2");
        when(mockResultSet.getString(4)).thenReturn("2020", "2021");
        when(mockResultSet.getDouble(5)).thenReturn(10.0, 20.0);
        when(mockResultSet.getInt(6)).thenReturn(0, 5);
        when(mockResultSet.getString(7)).thenReturn("tr1", "tr2");
        when(mockResultSet.getString(8)).thenReturn("i1.png", "i2.png");
        when(mockResultSet.getBoolean(9)).thenReturn(true, false);

        LibroDAO spyDao = spy(libroDAO);
        doReturn(Collections.emptyList()).when(spyDao).getScrittura(anyString());

        // Act
        List<Libro> list = spyDao.Search("query");

        // Assert
        assertNotNull(list);
        assertEquals(2, list.size());
        assertEquals("ISBN1", list.get(0).getIsbn());
        assertEquals("ISBN2", list.get(1).getIsbn());
    }

    @Test
    void testSearch_Empty_ReturnsEmptyList() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(false);

        // Act
        List<Libro> list = libroDAO.Search("nope");

        // Assert
        assertNotNull(list);
        assertTrue(list.isEmpty());
    }

    // ==================== doSave Tests ====================

    @Test
    void testDoSave_Success() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        Libro l = createTestLibro("NEWISBN", "T", 9.9, 0);
        Autore a = new Autore();
        a.setCf("CFA");
        List<Autore> aut = new ArrayList<>();
        aut.add(a);
        l.setAutori(aut);

        LibroDAO spyDao = spy(libroDAO);
        doNothing().when(spyDao).addAutore(eq("NEWISBN"), any(Autore.class));

        // Act
        assertDoesNotThrow(() -> spyDao.doSave(l));

        // Assert
        verify(mockPreparedStatement).setString(1, "NEWISBN");
        verify(mockPreparedStatement).executeUpdate();
        verify(spyDao).addAutore(eq("NEWISBN"), any(Autore.class));
    }

    @Test
    void testDoSave_InsertFails() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(contains("INSERT INTO Libro"))).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(0);

        Libro l = createTestLibro("BAD", "T", 1.0, 0);
        l.setAutori(new ArrayList<>());

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, () -> libroDAO.doSave(l));
        assertEquals("INSERT error.", exception.getMessage());
    }

    // ==================== deleteLibro Tests ====================

    @Test
    void testDeleteLibro_Success() throws SQLException {
        // Arrange
        PreparedStatement ps1 = mock(PreparedStatement.class);
        PreparedStatement ps2 = mock(PreparedStatement.class);
        PreparedStatement ps3 = mock(PreparedStatement.class);
        PreparedStatement ps4 = mock(PreparedStatement.class);
        PreparedStatement ps5 = mock(PreparedStatement.class);
        PreparedStatement ps6 = mock(PreparedStatement.class);

        when(mockConnection.prepareStatement(anyString())).thenReturn(ps1, ps2, ps3, ps4, ps5, ps6);
        when(ps1.executeUpdate()).thenReturn(1);
        when(ps2.executeUpdate()).thenReturn(1);
        when(ps3.executeUpdate()).thenReturn(1);
        when(ps4.executeUpdate()).thenReturn(1);
        when(ps5.executeUpdate()).thenReturn(1);
        when(ps6.executeUpdate()).thenReturn(1);

        // Act
        assertDoesNotThrow(() -> libroDAO.deleteLibro("GOODISBN"));

        // Assert
        verify(ps6).setString(1, "GOODISBN");
        verify(ps6).executeUpdate();
    }

    @Test
    void testDeleteLibro_FirstDeleteFails() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(0);

        // Act & Assert
        assertThrows(RuntimeException.class, () -> libroDAO.deleteLibro("ISBN_DEL_FAIL"));
    }

    @Test
    void testDeleteLibro_MiddleDeleteFails() throws SQLException {
        // Arrange
        PreparedStatement ps1 = mock(PreparedStatement.class);
        PreparedStatement ps2 = mock(PreparedStatement.class);
        PreparedStatement ps3 = mock(PreparedStatement.class);
        PreparedStatement ps4 = mock(PreparedStatement.class);
        PreparedStatement ps5 = mock(PreparedStatement.class);
        PreparedStatement ps6 = mock(PreparedStatement.class);

        when(mockConnection.prepareStatement(anyString())).thenReturn(ps1, ps2, ps3, ps4, ps5, ps6);
        when(ps1.executeUpdate()).thenReturn(1);
        when(ps2.executeUpdate()).thenReturn(1);
        when(ps3.executeUpdate()).thenReturn(0);
        when(ps4.executeUpdate()).thenReturn(1);
        when(ps5.executeUpdate()).thenReturn(1);
        when(ps6.executeUpdate()).thenReturn(1);

        // Act & Assert
        assertThrows(RuntimeException.class, () -> libroDAO.deleteLibro("MIDFAIL"));
    }

    @Test
    void testDeleteLibro_Delete4Fails() throws SQLException {
        // Arrange
        PreparedStatement ps1 = mock(PreparedStatement.class);
        PreparedStatement ps2 = mock(PreparedStatement.class);
        PreparedStatement ps3 = mock(PreparedStatement.class);
        PreparedStatement ps4 = mock(PreparedStatement.class);
        PreparedStatement ps5 = mock(PreparedStatement.class);
        PreparedStatement ps6 = mock(PreparedStatement.class);

        when(mockConnection.prepareStatement(anyString())).thenReturn(ps1, ps2, ps3, ps4, ps5, ps6);
        when(ps1.executeUpdate()).thenReturn(1);
        when(ps2.executeUpdate()).thenReturn(1);
        when(ps3.executeUpdate()).thenReturn(1);
        when(ps4.executeUpdate()).thenReturn(0);
        when(ps5.executeUpdate()).thenReturn(1);
        when(ps6.executeUpdate()).thenReturn(1);

        // Act & Assert
        assertThrows(RuntimeException.class, () -> libroDAO.deleteLibro("DEL4"));
    }

    @Test
    void testDeleteLibro_Delete5Fails() throws SQLException {
        // Arrange
        PreparedStatement ps1 = mock(PreparedStatement.class);
        PreparedStatement ps2 = mock(PreparedStatement.class);
        PreparedStatement ps3 = mock(PreparedStatement.class);
        PreparedStatement ps4 = mock(PreparedStatement.class);
        PreparedStatement ps5 = mock(PreparedStatement.class);
        PreparedStatement ps6 = mock(PreparedStatement.class);

        when(mockConnection.prepareStatement(anyString())).thenReturn(ps1, ps2, ps3, ps4, ps5, ps6);
        when(ps1.executeUpdate()).thenReturn(1);
        when(ps2.executeUpdate()).thenReturn(1);
        when(ps3.executeUpdate()).thenReturn(1);
        when(ps4.executeUpdate()).thenReturn(1);
        when(ps5.executeUpdate()).thenReturn(0);
        when(ps6.executeUpdate()).thenReturn(1);

        // Act & Assert
        assertThrows(RuntimeException.class, () -> libroDAO.deleteLibro("DEL5"));
    }

    @Test
    void testDeleteLibro_LastDeleteFails() throws SQLException {
        // Arrange
        PreparedStatement ps1 = mock(PreparedStatement.class);
        PreparedStatement ps2 = mock(PreparedStatement.class);
        PreparedStatement ps3 = mock(PreparedStatement.class);
        PreparedStatement ps4 = mock(PreparedStatement.class);
        PreparedStatement ps5 = mock(PreparedStatement.class);
        PreparedStatement ps6 = mock(PreparedStatement.class);

        when(mockConnection.prepareStatement(anyString())).thenReturn(ps1, ps2, ps3, ps4, ps5, ps6);
        when(ps1.executeUpdate()).thenReturn(1);
        when(ps2.executeUpdate()).thenReturn(1);
        when(ps3.executeUpdate()).thenReturn(1);
        when(ps4.executeUpdate()).thenReturn(1);
        when(ps5.executeUpdate()).thenReturn(1);
        when(ps6.executeUpdate()).thenReturn(0);

        // Act & Assert
        assertThrows(RuntimeException.class, () -> libroDAO.deleteLibro("LASTFAIL"));
    }

    // ==================== updateLibro Tests ====================

    @Test
    void testUpdateLibro_Success() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(contains("UPDATE Libro SET"))).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        Libro l = createTestLibro("U1", "T", 4.5, 2);

        // Act
        assertDoesNotThrow(() -> libroDAO.updateLibro(l));

        // Assert
        verify(mockPreparedStatement).setString(1, "T");
        verify(mockPreparedStatement).setString(8, "U1");
        verify(mockPreparedStatement).executeUpdate();
    }

    @Test
    void testUpdateLibro_NoRowsUpdated() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(0);

        Libro l = createTestLibro("ISBNUP", "T", 5.0, 1);

        // Act & Assert
        assertThrows(RuntimeException.class, () -> libroDAO.updateLibro(l));
    }

    // ==================== updateLibroSconto Tests ====================

    @Test
    void testUpdateLibroSconto_Success() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(contains("UPDATE Libro SET sconto"))).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        Libro l = createTestLibro("S1", "T", 10.0, 20);

        // Act
        assertDoesNotThrow(() -> libroDAO.updateLibroSconto(l));

        // Assert
        verify(mockPreparedStatement).setInt(1, 20);
        verify(mockPreparedStatement).setString(2, "S1");
        verify(mockPreparedStatement).executeUpdate();
    }

    @Test
    void testUpdateLibroSconto_NoRowsUpdated() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(contains("UPDATE Libro SET sconto"))).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(0);

        Libro l = createTestLibro("ISBNUP", "T", 10.0, 15);

        // Act & Assert
        assertThrows(RuntimeException.class, () -> libroDAO.updateLibroSconto(l));
    }

    // ==================== updateDisponibile Tests ====================

    @Test
    void testUpdateDisponibile_Success() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(contains("UPDATE Libro SET disponibile"))).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        Libro l = createTestLibro("U2", "T", 10.0, 0);
        l.setDisponibile(true);

        // Act
        assertDoesNotThrow(() -> libroDAO.updateDisponibile(l));

        // Assert
        verify(mockPreparedStatement).setBoolean(1, true);
        verify(mockPreparedStatement).setString(2, "U2");
        verify(mockPreparedStatement).executeUpdate();
    }

    @Test
    void testUpdateDisponibile_NoRowsUpdated() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(0);

        Libro l = createTestLibro("ISBNAV", "T", 10.0, 0);
        l.setDisponibile(true);

        // Act & Assert
        assertThrows(RuntimeException.class, () -> libroDAO.updateDisponibile(l));
    }

    // ==================== addAutore Tests ====================

    @Test
    void testAddAutore_NewAuthor_SavesAndInserts() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        Autore newAut = new Autore();
        newAut.setCf("CFA");

        try (MockedConstruction<AutoreDAO> mocked = mockConstruction(AutoreDAO.class,
                (mock, ctx) -> when(mock.searchAutore("CFA")).thenReturn(null))) {

            // Act
            libroDAO.addAutore("ISBNX", newAut);

            // Assert
            verify(mockPreparedStatement).setString(1, "CFA");
            verify(mockPreparedStatement).setString(2, "ISBNX");
            verify(mockPreparedStatement).executeUpdate();

            AutoreDAO constructed = mocked.constructed().get(0);
            verify(constructed).doSave(newAut);
        }
    }

    @Test
    void testAddAutore_ExistingAuthor_DoesNotSave() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        try (MockedConstruction<AutoreDAO> mocked = mockConstruction(AutoreDAO.class,
                (mock, ctx) -> when(mock.searchAutore("CFA")).thenReturn(new Autore()))) {

            Autore a = new Autore();
            a.setCf("CFA");

            // Act
            libroDAO.addAutore("ISBN_EXIST", a);

            // Assert
            AutoreDAO constructed = mocked.constructed().get(0);
            verify(constructed, never()).doSave(any(Autore.class));
            verify(mockPreparedStatement).executeUpdate();
        }
    }

    @Test
    void testAddAutore_InsertFails() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(contains("INSERT INTO Scrittura"))).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(0);

        try (MockedConstruction<AutoreDAO> mocked = mockConstruction(AutoreDAO.class,
                (mock, ctx) -> when(mock.searchAutore("CFX")).thenReturn(new Autore()))) {

            Autore a = new Autore();
            a.setCf("CFX");

            // Act & Assert
            assertThrows(RuntimeException.class, () -> libroDAO.addAutore("ISBNX", a));
        }
    }

    // ==================== deleteAutoreScrittura Tests ====================

    @Test
    void testDeleteAutoreScrittura_Success() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(contains("DELETE FROM Scrittura"))).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        try (MockedConstruction<AutoreDAO> mocked = mockConstruction(AutoreDAO.class,
                (mock, ctx) -> doNothing().when(mock).deleteAutore("CFAUT"))) {

            Autore a = new Autore();
            a.setCf("CFAUT");

            // Act
            assertDoesNotThrow(() -> libroDAO.deleteAutoreScrittura("ISBNDEL", a));

            // Assert
            verify(mockPreparedStatement).setString(1, "ISBNDEL");
            verify(mockPreparedStatement).setString(2, "CFAUT");
            verify(mockPreparedStatement).executeUpdate();

            AutoreDAO constructed = mocked.constructed().get(0);
            verify(constructed).deleteAutore("CFAUT");
        }
    }

    @Test
    void testDeleteAutoreScrittura_ExecuteUpdateFails() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(contains("DELETE FROM Scrittura"))).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(0);

        try (MockedConstruction<AutoreDAO> mocked = mockConstruction(AutoreDAO.class,
                (mock, ctx) -> doNothing().when(mock).deleteAutore("CFA"))) {

            Autore a = new Autore();
            a.setCf("CFA");

            // Act & Assert
            assertThrows(RuntimeException.class, () -> libroDAO.deleteAutoreScrittura("ISBNX", a));
        }
    }

    // ==================== getScrittura Tests ====================

    @Test
    void testGetScrittura_ReturnsAuthorWhenPresent() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(contains("SELECT cf FROM Scrittura"))).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true, false);
        when(mockResultSet.getString(1)).thenReturn("CFAUTH");

        Autore a = new Autore();
        a.setCf("CFAUTH");
        a.setNome("N");

        try (MockedConstruction<AutoreDAO> mocked = mockConstruction(AutoreDAO.class,
                (mock, ctx) -> when(mock.searchAutore("CFAUTH")).thenReturn(a))) {

            // Act
            List<Autore> list = libroDAO.getScrittura("ISBNX");

            // Assert
            assertNotNull(list);
            assertEquals(1, list.size());
            assertEquals(a, list.get(0));
        }
    }

    @Test
    void testGetScrittura_ReturnsNullWhenAuthorMissing() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(contains("SELECT cf FROM Scrittura"))).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true, false);
        when(mockResultSet.getString(1)).thenReturn("CFNULL");

        try (MockedConstruction<AutoreDAO> mocked = mockConstruction(AutoreDAO.class,
                (mock, ctx) -> when(mock.searchAutore("CFNULL")).thenReturn(null))) {

            // Act
            List<Autore> list = libroDAO.getScrittura("ISBNZ");

            // Assert
            assertNotNull(list);
            assertEquals(1, list.size());
            assertNull(list.get(0));
        }
    }

    // ==================== getAppartenenzaReparto Tests ====================

    @Test
    void testGetAppartenenzaReparto_ReturnsList() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(contains("Appartenenza"))).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true, false);
        when(mockResultSet.getInt(1)).thenReturn(3);

        Reparto reparto = new Reparto();
        reparto.setIdReparto(3);
        reparto.setDescrizione("desc");

        try (MockedConstruction<RepartoDAO> mocked = mockConstruction(RepartoDAO.class,
                (mock, ctx) -> when(mock.doRetrieveById(3)).thenReturn(reparto))) {

            // Act
            List<Reparto> list = libroDAO.getAppartenenzaReparto("ISBNR");

            // Assert
            assertNotNull(list);
            assertEquals(1, list.size());
            assertEquals(reparto, list.get(0));
        }
    }

    @Test
    void testGetAppartenenzaReparto_Empty_ReturnsEmptyList() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(contains("Appartenenza"))).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(false);

        // Act
        List<Reparto> list = libroDAO.getAppartenenzaReparto("ISBNNONE");

        // Assert
        assertNotNull(list);
        assertTrue(list.isEmpty());
    }

    // ==================== getPresenzaSede Tests ====================

    @Test
    void testGetPresenzaSede_ReturnsList() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(contains("Presenza"))).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true, false);
        when(mockResultSet.getInt(1)).thenReturn(7);

        Sede s = new Sede();
        s.setIdSede(7);
        s.setCitta("C");
        s.setVia("V");
        s.setCivico(1);
        s.setCap("00001");

        try (MockedConstruction<SedeDAO> mocked = mockConstruction(SedeDAO.class,
                (mock, ctx) -> when(mock.doRetrieveById(7)).thenReturn(s))) {

            // Act
            List<Sede> list = libroDAO.getPresenzaSede("ISBNS");

            // Assert
            assertNotNull(list);
            assertEquals(1, list.size());
            assertEquals(s, list.get(0));
        }
    }

    @Test
    void testGetPresenzaSede_Empty_ReturnsEmptyList() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(contains("Presenza"))).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(false);

        // Act
        List<Sede> list = libroDAO.getPresenzaSede("ISBNNONE");

        // Assert
        assertNotNull(list);
        assertTrue(list.isEmpty());
    }

}
