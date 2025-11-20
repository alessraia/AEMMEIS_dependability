package controller.admin.gestisciSedi;

import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.libroService.Sede;
import model.libroService.SedeDAO;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.MockedConstruction;

import java.io.IOException;
import java.util.ArrayList;

import static org.mockito.ArgumentMatchers.anyInt;
import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.Mockito.*;

/**
 * Unit tests for InsertLibroSedeServlet
 * Tests the servlet's ability to add books to store locations (sedi) and handle
 * multiple book additions with proper redirection.
 */
class InsertLibroSedeServletTest {

    private InsertLibroSedeServlet servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;

    @BeforeEach
    void setUp() {
        servlet = new InsertLibroSedeServlet();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
    }

    /**
     * Test successful addition of single book to sede
     * Scenario: One book ISBN is provided and added to sede
     */
    @Test
    void testDoGet_SuccessfulSingleBookAddition() throws IOException {
        // Arrange
        when(request.getParameter("idSede")).thenReturn("1");
        when(request.getParameterValues("isbn")).thenReturn(new String[]{"ISBN-001"});

        Sede sede = new Sede();
        sede.setIdSede(1);
        sede.setCitta("Milano");
        sede.setLibri(new ArrayList<>());

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(1)).thenReturn(sede);
            doNothing().when(mock).addLibroSede(sede, "ISBN-001");
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Verify redirect occurs
            verify(response).sendRedirect("gestisci-sedi");
        }
    }

    /**
     * Test addition of multiple books to sede
     * Scenario: Multiple book ISBNs are provided and all added to sede
     */
    @Test
    void testDoGet_SuccessfulMultipleBooksAddition() throws IOException {
        // Arrange
        when(request.getParameter("idSede")).thenReturn("2");
        when(request.getParameterValues("isbn")).thenReturn(
                new String[]{"ISBN-001", "ISBN-002", "ISBN-003"}
        );

        Sede sede = new Sede();
        sede.setIdSede(2);
        sede.setLibri(new ArrayList<>());

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(2)).thenReturn(sede);
            doNothing().when(mock).addLibroSede(eq(sede), anyString());
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Verify all books are added
            verify(mockedConstruction.constructed().get(0), times(3)).addLibroSede(eq(sede), anyString());
            verify(response).sendRedirect("gestisci-sedi");
        }
    }

    /**
     * Test with null ISBN array
     * Scenario: No books selected for addition (libriIsbn is null)
     */
    @Test
    void testDoGet_NullIsbnArray() throws IOException {
        // Arrange
        when(request.getParameter("idSede")).thenReturn("3");
        when(request.getParameterValues("isbn")).thenReturn(null);

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            // No need to mock anything as addLibroSede should not be called
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Should redirect without adding any books
            verify(response).sendRedirect("gestisci-sedi");
            // Verify addLibroSede is never called
            verify(mockedConstruction.constructed().get(0), never()).addLibroSede(any(), anyString());
        }
    }

    /**
     * Test with empty ISBN array
     * Scenario: ISBN parameter values array is empty
     */
    @Test
    void testDoGet_EmptyIsbnArray() throws IOException {
        // Arrange
        when(request.getParameter("idSede")).thenReturn("4");
        when(request.getParameterValues("isbn")).thenReturn(new String[]{});

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            // No books to add
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Should redirect with no books added
            verify(response).sendRedirect("gestisci-sedi");
        }
    }

    /**
     * Test correct sede retrieval
     * Scenario: Verify doRetrieveById is called with correct sede ID
     */
    @Test
    void testDoGet_CorrectSedeRetrieval() throws IOException {
        // Arrange
        when(request.getParameter("idSede")).thenReturn("5");
        when(request.getParameterValues("isbn")).thenReturn(new String[]{"ISBN-001"});

        Sede sede = new Sede();
        sede.setIdSede(5);
        sede.setLibri(new ArrayList<>());

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(5)).thenReturn(sede);
            doNothing().when(mock).addLibroSede(sede, "ISBN-001");
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Verify correct sede ID is used
            verify(mockedConstruction.constructed().get(0)).doRetrieveById(5);
        }
    }

    /**
     * Test each book is added individually
     * Scenario: Verify each ISBN in the array is processed
     */
    @Test
    void testDoGet_EachBookAddedIndividually() throws IOException {
        // Arrange
        when(request.getParameter("idSede")).thenReturn("6");
        String[] isbns = {"ISBN-A", "ISBN-B", "ISBN-C"};
        when(request.getParameterValues("isbn")).thenReturn(isbns);

        Sede sede = new Sede();
        sede.setIdSede(6);
        sede.setLibri(new ArrayList<>());

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(6)).thenReturn(sede);
            doNothing().when(mock).addLibroSede(eq(sede), anyString());
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Each ISBN should be added once
            verify(mockedConstruction.constructed().get(0)).addLibroSede(sede, "ISBN-A");
            verify(mockedConstruction.constructed().get(0)).addLibroSede(sede, "ISBN-B");
            verify(mockedConstruction.constructed().get(0)).addLibroSede(sede, "ISBN-C");
        }
    }

    /**
     * Test exception handling during book addition
     * Scenario: RuntimeException during addLibroSede is propagated
     */
    @Test
    void testDoGet_ExceptionDuringBookAddition() throws IOException {
        // Arrange
        when(request.getParameter("idSede")).thenReturn("7");
        when(request.getParameterValues("isbn")).thenReturn(new String[]{"ISBN-001"});

        Sede sede = new Sede();
        sede.setIdSede(7);
        sede.setLibri(new ArrayList<>());

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(7)).thenReturn(sede);
            doThrow(new RuntimeException("INSERT error.")).when(mock).addLibroSede(sede, "ISBN-001");
        })) {
            // Act & Assert
            try {
                servlet.doGet(request, response);
            } catch (RuntimeException e) {
                assert e.getMessage().contains("INSERT error");
            }
        }
    }

    /**
     * Test redirect occurs after all books added
     * Scenario: Redirect should happen after loop completes
     */
    @Test
    void testDoGet_RedirectAfterAllBooksAdded() throws IOException {
        // Arrange
        when(request.getParameter("idSede")).thenReturn("8");
        when(request.getParameterValues("isbn")).thenReturn(
                new String[]{"ISBN-1", "ISBN-2", "ISBN-3"}
        );

        Sede sede = new Sede();
        sede.setIdSede(8);
        sede.setLibri(new ArrayList<>());

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(8)).thenReturn(sede);
            doNothing().when(mock).addLibroSede(eq(sede), anyString());
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Verify redirect is called exactly once and after additions
            verify(response, times(1)).sendRedirect("gestisci-sedi");
        }
    }

    /**
     * Test correct redirect URL
     * Scenario: Verify exact redirect path
     */
    @Test
    void testDoGet_CorrectRedirectUrl() throws IOException {
        // Arrange
        when(request.getParameter("idSede")).thenReturn("9");
        when(request.getParameterValues("isbn")).thenReturn(new String[]{"ISBN-001"});

        Sede sede = new Sede();
        sede.setIdSede(9);
        sede.setLibri(new ArrayList<>());

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(9)).thenReturn(sede);
            doNothing().when(mock).addLibroSede(sede, "ISBN-001");
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Verify exact redirect URL
            verify(response).sendRedirect("gestisci-sedi");
        }
    }

    /**
     * Test large number of books
     * Scenario: Multiple books are added to sede
     */
    @Test
    void testDoGet_LargeNumberOfBooks() throws IOException {
        // Arrange
        when(request.getParameter("idSede")).thenReturn("10");
        String[] manyIsbns = new String[50];
        for (int i = 0; i < 50; i++) {
            manyIsbns[i] = "ISBN-" + i;
        }
        when(request.getParameterValues("isbn")).thenReturn(manyIsbns);

        Sede sede = new Sede();
        sede.setIdSede(10);
        sede.setLibri(new ArrayList<>());

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(10)).thenReturn(sede);
            doNothing().when(mock).addLibroSede(eq(sede), anyString());
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: All 50 books should be added
            verify(mockedConstruction.constructed().get(0), times(50)).addLibroSede(eq(sede), anyString());
        }
    }

    /**
     * Test with single book ISBN
     * Scenario: Only one book is added
     */
    @Test
    void testDoGet_SingleBookIsbn() throws IOException {
        // Arrange
        when(request.getParameter("idSede")).thenReturn("11");
        when(request.getParameterValues("isbn")).thenReturn(new String[]{"SINGLE-ISBN"});

        Sede sede = new Sede();
        sede.setIdSede(11);
        sede.setLibri(new ArrayList<>());

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(11)).thenReturn(sede);
            doNothing().when(mock).addLibroSede(sede, "SINGLE-ISBN");
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            verify(mockedConstruction.constructed().get(0)).addLibroSede(sede, "SINGLE-ISBN");
            verify(response).sendRedirect("gestisci-sedi");
        }
    }

    /**
     * Test SedeDAO instantiation
     * Scenario: Verify SedeDAO is created exactly once
     */
    @Test
    void testDoGet_SedeDAOInstantiated() throws IOException {
        // Arrange
        when(request.getParameter("idSede")).thenReturn("12");
        when(request.getParameterValues("isbn")).thenReturn(new String[]{"ISBN-001"});

        Sede sede = new Sede();
        sede.setIdSede(12);
        sede.setLibri(new ArrayList<>());

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(12)).thenReturn(sede);
            doNothing().when(mock).addLibroSede(sede, "ISBN-001");
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: SedeDAO should be instantiated exactly once
            assert mockedConstruction.constructed().size() == 1;
        }
    }

    /**
     * Test ISBN parameter is parsed correctly
     * Scenario: String ISBN is passed correctly to addLibroSede
     */
    @Test
    void testDoGet_IsbnParameterParsing() throws IOException {
        // Arrange
        when(request.getParameter("idSede")).thenReturn("13");
        String[] testIsbns = {"978-3-16-148410-0", "ISBN123ABC", "0-7432-7356-5"};
        when(request.getParameterValues("isbn")).thenReturn(testIsbns);

        Sede sede = new Sede();
        sede.setIdSede(13);
        sede.setLibri(new ArrayList<>());

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(13)).thenReturn(sede);
            doNothing().when(mock).addLibroSede(eq(sede), anyString());
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Each ISBN should be passed as-is
            verify(mockedConstruction.constructed().get(0)).addLibroSede(sede, "978-3-16-148410-0");
            verify(mockedConstruction.constructed().get(0)).addLibroSede(sede, "ISBN123ABC");
            verify(mockedConstruction.constructed().get(0)).addLibroSede(sede, "0-7432-7356-5");
        }
    }

    /**
     * Test multiple sequential operations
     * Scenario: Servlet handles multiple requests in sequence
     */
    @Test
    void testDoGet_MultipleSequentialOperations() throws IOException {
        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(anyInt())).thenReturn(createTestSede());
            doNothing().when(mock).addLibroSede(any(), anyString());
        })) {
            // Act: Execute multiple operations
            for (int i = 1; i <= 3; i++) {
                when(request.getParameter("idSede")).thenReturn(String.valueOf(i));
                when(request.getParameterValues("isbn")).thenReturn(new String[]{"ISBN-" + i});
                servlet.doGet(request, response);
            }

            // Assert: Each operation should result in redirect
            verify(response, times(3)).sendRedirect("gestisci-sedi");
        }
    }

    /**
     * Test no addLibroSede call when ISBN array is null
     * Scenario: If libriIsbn is null, addLibroSede should not be called
     */
    @Test
    void testDoGet_NoAddLibroSedeWhenIsbnNull() throws IOException {
        // Arrange
        when(request.getParameter("idSede")).thenReturn("14");
        when(request.getParameterValues("isbn")).thenReturn(null);

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            // Setup won't include addLibroSede
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: addLibroSede should never be called
            verify(mockedConstruction.constructed().get(0), never()).addLibroSede(any(), anyString());
        }
    }

    /**
     * Test with duplicate ISBN values
     * Scenario: Same ISBN appears multiple times in array
     */
    @Test
    void testDoGet_DuplicateIsbnValues() throws IOException {
        // Arrange
        when(request.getParameter("idSede")).thenReturn("15");
        when(request.getParameterValues("isbn")).thenReturn(
                new String[]{"ISBN-001", "ISBN-001", "ISBN-002", "ISBN-001"}
        );

        Sede sede = new Sede();
        sede.setIdSede(15);
        sede.setLibri(new ArrayList<>());

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(15)).thenReturn(sede);
            doNothing().when(mock).addLibroSede(eq(sede), anyString());
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Each ISBN in array should be processed (duplicates included)
            verify(mockedConstruction.constructed().get(0), times(4)).addLibroSede(eq(sede), anyString());
        }
    }

    /**
     * Test with special characters in ISBN
     * Scenario: ISBN may contain special characters
     */
    @Test
    void testDoGet_SpecialCharactersInIsbn() throws IOException {
        // Arrange
        when(request.getParameter("idSede")).thenReturn("16");
        when(request.getParameterValues("isbn")).thenReturn(
                new String[]{"ISBN-001", "ISBN@002", "ISBN#003"}
        );

        Sede sede = new Sede();
        sede.setIdSede(16);
        sede.setLibri(new ArrayList<>());

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(16)).thenReturn(sede);
            doNothing().when(mock).addLibroSede(eq(sede), anyString());
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Special characters should be preserved
            verify(mockedConstruction.constructed().get(0)).addLibroSede(sede, "ISBN-001");
            verify(mockedConstruction.constructed().get(0)).addLibroSede(sede, "ISBN@002");
            verify(mockedConstruction.constructed().get(0)).addLibroSede(sede, "ISBN#003");
        }
    }

    /**
     * Helper method to create a test sede
     *
     * @return A Sede object with basic properties
     */
    private Sede createTestSede() {
        Sede sede = new Sede();
        sede.setIdSede(1);
        sede.setCitta("Test City");
        sede.setVia("Test Street");
        sede.setCivico(1);
        sede.setCap("12345");
        sede.setLibri(new ArrayList<>());
        return sede;
    }
}
